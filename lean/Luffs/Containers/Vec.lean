import Luffs.Containers.Box

set_option autoImplicit false

namespace Luffs.Containers.Vec

open Luffs.Memory
open Luffs.Allocator.TLSF
open Iris Iris.BI

def encodeValues {α : Type} (codec : Codec α) (values : List α) : List Byte :=
  values.flatMap codec.encode

theorem encodeValues_append {α : Type} (codec : Codec α)
    (left right : List α) :
    encodeValues codec (left ++ right) =
      encodeValues codec left ++ encodeValues codec right := by
  simp [encodeValues, List.flatMap_append]

theorem encodeValues_length {α : Type} (codec : Codec α) (values : List α) :
    (encodeValues codec values).length = values.length * codec.size := by
  induction values with
  | nil => simp [encodeValues]
  | cons value rest ih =>
      change (codec.encode value ++ encodeValues codec rest).length =
        (rest.length + 1) * codec.size
      rw [List.length_append, codec.encode_length, ih, Nat.add_mul]
      omega

theorem encodeValues_split_at {α : Type} (codec : Codec α)
    (values : List α) {i : Nat} (hi : i < values.length) :
    encodeValues codec values =
      encodeValues codec (values.take i) ++
        (codec.encode values[i] ++ encodeValues codec (values.drop (i + 1))) := by
  calc
    encodeValues codec values =
        encodeValues codec (values.take i ++ values.drop i) :=
      congrArg (encodeValues codec) (List.take_append_drop i values).symm
    _ = encodeValues codec (values.take i) ++ encodeValues codec (values.drop i) :=
      encodeValues_append codec _ _
    _ = encodeValues codec (values.take i) ++
        (codec.encode values[i] ++
          encodeValues codec (values.drop (i + 1))) := by
      rw [List.drop_eq_getElem_cons hi]
      rfl

structure Handle where
  block : Block
  len : Nat
  capacity : Nat
deriving DecidableEq, Repr

structure SliceHandle where
  begin : Nat
  «end» : Nat
deriving DecidableEq, Repr

def Valid {α : Type} (codec : Codec α) (handle : Handle) : Prop :=
  handle.len ≤ handle.capacity ∧
    handle.capacity * codec.size ≤ handle.block.bytes

def SliceValid (handle : Handle) (slice : SliceHandle) : Prop :=
  slice.begin ≤ slice.end ∧ slice.end ≤ handle.len

def sliceValues {α : Type} (values : List α) (slice : SliceHandle) : List α :=
  (values.drop slice.begin).take (slice.end - slice.begin)

def sliceRegion {α : Type} (codec : Codec α) (pool : Region)
    (handle : Handle) (slice : SliceHandle) : Region :=
  { base := (handle.block.region pool).base + slice.begin * codec.size
    bytes := (slice.end - slice.begin) * codec.size }

theorem sliceRegion_fits {α : Type} {codec : Codec α} {handle : Handle}
    (hvalid : Valid codec handle) {slice : SliceHandle}
    (hslice : SliceValid handle slice) :
    slice.begin * codec.size + (slice.end - slice.begin) * codec.size ≤
      handle.block.bytes := by
  rcases hvalid with ⟨hlen, hcapacity⟩
  rcases hslice with ⟨hbegin, hend⟩
  have hendCapacity : slice.end ≤ handle.capacity := Nat.le_trans hend hlen
  have hbytes := Nat.mul_le_mul_right codec.size hendCapacity
  rw [← Nat.add_mul, Nat.add_sub_of_le hbegin]
  exact Nat.le_trans hbytes hcapacity

theorem values_slice_decomposition {α : Type} (values : List α)
    (slice : SliceHandle) (hbegin : slice.begin ≤ slice.end)
    (hend : slice.end ≤ values.length) :
    values = values.take slice.begin ++ sliceValues values slice ++
      values.drop slice.end := by
  have hbeginLen : slice.begin ≤ values.length := Nat.le_trans hbegin hend
  have hdrop : (values.drop slice.begin).drop (slice.end - slice.begin) =
      values.drop slice.end := by
    rw [List.drop_drop, Nat.add_sub_of_le hbegin]
  calc
    values = values.take slice.begin ++ values.drop slice.begin :=
      (List.take_append_drop slice.begin values).symm
    _ = values.take slice.begin ++
        ((values.drop slice.begin).take (slice.end - slice.begin) ++
          (values.drop slice.begin).drop (slice.end - slice.begin)) := by
      exact congrArg (values.take slice.begin ++ ·)
        (List.take_append_drop (slice.end - slice.begin)
          (values.drop slice.begin)).symm
    _ = values.take slice.begin ++ sliceValues values slice ++
        values.drop slice.end := by
      simp only [sliceValues, hdrop, List.append_assoc]

theorem encodeValues_slice_decomposition {α : Type} (codec : Codec α)
    (values : List α) (slice : SliceHandle) (hbegin : slice.begin ≤ slice.end)
    (hend : slice.end ≤ values.length) :
    encodeValues codec values =
      encodeValues codec (values.take slice.begin) ++
        (encodeValues codec (sliceValues values slice) ++
          encodeValues codec (values.drop slice.end)) := by
  have hdecomp := values_slice_decomposition values slice hbegin hend
  calc
    encodeValues codec values = encodeValues codec
        (values.take slice.begin ++ sliceValues values slice ++
          values.drop slice.end) := congrArg (encodeValues codec) hdecomp
    _ = encodeValues codec (values.take slice.begin) ++
        (encodeValues codec (sliceValues values slice) ++
          encodeValues codec (values.drop slice.end)) := by
      rw [encodeValues_append, encodeValues_append, List.append_assoc]

structure AllocResult where
  handle : Handle
  state : Alloc.State

def allocationBytes {α : Type} (codec : Codec α) (capacity : Nat) : Nat :=
  Box.requestBytes (capacity * codec.size)

theorem roundUp8_eq_allocationBytes {α : Type} (codec : Codec α)
    {capacity : Nat} (hcapacity : 0 < capacity) :
    roundUp8 (capacity * codec.size) = allocationBytes codec capacity := by
  exact roundUp8_eq_linearBinUpper (capacity * codec.size)
    (Nat.mul_pos hcapacity codec.size_pos)

theorem allocationBytes_positive {α : Type} (codec : Codec α) {capacity : Nat}
    (hcapacity : 0 < capacity) : 0 < allocationBytes codec capacity :=
  Box.requestBytes_positive (Nat.mul_pos hcapacity codec.size_pos)

theorem allocationBytes_fits {α : Type} (codec : Codec α) {capacity : Nat}
    (hcapacity : 0 < capacity) :
    capacity * codec.size ≤ allocationBytes codec capacity :=
  Box.requestBytes_fits (Nat.mul_pos hcapacity codec.size_pos)

def allocate {α : Type} (codec : Codec α) (capacity : Nat)
    (hcapacity : 0 < capacity) (state : Alloc.State)
    (hkeyMax : requestKey (allocationBytes codec capacity) <
      2 ^ firstLevelCount) : Option AllocResult :=
  match Alloc.allocate state (allocationBytes codec capacity)
      (allocationBytes_positive codec hcapacity) hkeyMax with
  | none => none
  | some result => some ⟨⟨result.allocated, 0, capacity⟩, result.state⟩

theorem allocate_result {α : Type} {codec : Codec α} {capacity : Nat}
    {hcapacity : 0 < capacity} {state : Alloc.State}
    {hkeyMax : requestKey (allocationBytes codec capacity) <
      2 ^ firstLevelCount} {result : AllocResult}
    (hsuccess : allocate codec capacity hcapacity state hkeyMax = some result) :
    ∃ raw, Alloc.allocate state (allocationBytes codec capacity)
        (allocationBytes_positive codec hcapacity) hkeyMax = some raw ∧
      result.handle = ⟨raw.allocated, 0, capacity⟩ ∧
      result.state = raw.state := by
  unfold allocate at hsuccess
  cases hraw : Alloc.allocate state (allocationBytes codec capacity)
      (allocationBytes_positive codec hcapacity) hkeyMax with
  | none => simp [hraw] at hsuccess
  | some raw =>
      simp [hraw] at hsuccess
      subst result
      exact ⟨raw, rfl, rfl, rfl⟩

theorem allocate_safe {α : Type} {codec : Codec α} {capacity : Nat}
    {hcapacity : 0 < capacity} {pool : Region} {state : Alloc.State}
    (hvalid : Alloc.Valid pool state)
    {hkeyMax : requestKey (allocationBytes codec capacity) <
      2 ^ firstLevelCount} {result : AllocResult}
    (hsuccess : allocate codec capacity hcapacity state hkeyMax = some result) :
    Valid codec result.handle ∧ result.handle.block.free = false ∧
      result.handle.block.aligned ∧ Alloc.Valid pool result.state := by
  obtain ⟨raw, hraw, hhandle, hstate⟩ := allocate_result hsuccess
  rw [hhandle, hstate]
  have hsafe := Alloc.allocate_safe hvalid hraw
  have hpreserved := Alloc.allocate_preserves_valid hvalid
    (Box.requestBytes_aligned (capacity * codec.size)) hraw
  exact ⟨⟨by simp, Nat.le_trans (allocationBytes_fits codec hcapacity)
      hsafe.2.2.1⟩, hsafe.1, hsafe.2.1, hpreserved⟩

theorem allocate_complete {α : Type} {codec : Codec α} {capacity : Nat}
    {hcapacity : 0 < capacity} {pool : Region} {state : Alloc.State}
    (hvalid : Alloc.Valid pool state)
    {hkeyMax : requestKey (allocationBytes codec capacity) <
      2 ^ firstLevelCount}
    (heligible : Bins.HasEligibleBin state.bins
      (searchSizeClass (allocationBytes codec capacity)
        (allocationBytes_positive codec hcapacity) hkeyMax)) :
    ∃ result, allocate codec capacity hcapacity state hkeyMax = some result := by
  obtain ⟨raw, hraw⟩ := Alloc.allocate_complete hvalid
    (Box.requestBytes_aligned (capacity * codec.size)) heligible
  change Alloc.allocate state (allocationBytes codec capacity)
    (allocationBytes_positive codec hcapacity) hkeyMax = some raw at hraw
  exact ⟨⟨⟨raw.allocated, 0, capacity⟩, raw.state⟩, by
    simp [allocate, hraw]⟩

def push (handle : Handle) : Option Handle :=
  if handle.len < handle.capacity then
    some { handle with len := handle.len + 1 }
  else none

def pop (handle : Handle) : Option Handle :=
  if 0 < handle.len then some { handle with len := handle.len - 1 } else none

theorem push_result {handle next : Handle} (hsuccess : push handle = some next) :
    handle.len < handle.capacity ∧ next = { handle with len := handle.len + 1 } := by
  unfold push at hsuccess
  split at hsuccess
  next hlt => exact ⟨hlt, Option.some.inj hsuccess |>.symm⟩
  next => contradiction

theorem push_preserves_valid {α : Type} {codec : Codec α}
    {handle next : Handle} (hvalid : Valid codec handle)
    (hsuccess : push handle = some next) : Valid codec next := by
  obtain ⟨hlt, rfl⟩ := push_result hsuccess
  rcases hvalid with ⟨hlen, hcapacity⟩
  exact ⟨by simp; omega, by simpa [Valid] using hcapacity⟩

theorem pop_result {handle next : Handle} (hsuccess : pop handle = some next) :
    0 < handle.len ∧ next = { handle with len := handle.len - 1 } := by
  unfold pop at hsuccess
  split at hsuccess
  next hpos => exact ⟨hpos, Option.some.inj hsuccess |>.symm⟩
  next => contradiction

theorem pop_preserves_valid {α : Type} {codec : Codec α}
    {handle next : Handle} (hvalid : Valid codec handle)
    (hsuccess : pop handle = some next) : Valid codec next := by
  obtain ⟨hpos, rfl⟩ := pop_result hsuccess
  rcases hvalid with ⟨hlen, hcapacity⟩
  exact ⟨by simp; omega, by simpa [Valid] using hcapacity⟩

def Owns {GF : BundledGFunctors} [ByteRegionGS GF] [ByteContentsGS GF]
    {α : Type} (codec : Codec α) (pool : Region) (handle : Handle)
    (values : List α) : IProp GF :=
  iprop(OwnsBytes (handle.block.region pool) ∗
    PointsToBytes (handle.block.region pool).base (encodeValues codec values))

def slicePrefixRegion {α : Type} (codec : Codec α) (pool : Region)
    (handle : Handle) (slice : SliceHandle) : Region :=
  { base := (handle.block.region pool).base
    bytes := slice.begin * codec.size }

def sliceTailRegion {α : Type} (codec : Codec α) (pool : Region)
    (handle : Handle) (slice : SliceHandle) : Region :=
  { base := (handle.block.region pool).base + slice.end * codec.size
    bytes := handle.block.bytes - slice.end * codec.size }

def MutSliceOwns {GF : BundledGFunctors}
    [ByteRegionGS GF] [ByteContentsGS GF] {α : Type}
    (codec : Codec α) (pool : Region) (handle : Handle) (slice : SliceHandle)
    (values : List α) : IProp GF :=
  iprop(OwnsBytes (sliceRegion codec pool handle slice) ∗
    PointsToBytes (sliceRegion codec pool handle slice).base
      (encodeValues codec values))

def MutSliceRest {GF : BundledGFunctors}
    [ByteRegionGS GF] [ByteContentsGS GF] {α : Type}
    (codec : Codec α) (pool : Region) (handle : Handle) (slice : SliceHandle)
    (prefixValues suffixValues : List α) : IProp GF :=
  iprop((OwnsBytes (slicePrefixRegion codec pool handle slice) ∗
      OwnsBytes (sliceTailRegion codec pool handle slice)) ∗
    (PointsToBytes (handle.block.region pool).base
        (encodeValues codec prefixValues) ∗
      PointsToBytes ((handle.block.region pool).base +
          slice.end * codec.size) (encodeValues codec suffixValues)))

theorem mutSlice_owns_exclusive {GF : BundledGFunctors}
    [ByteRegionGS GF] [ByteContentsGS GF] {α : Type}
    (codec : Codec α) (pool : Region) (handle : Handle) (slice : SliceHandle)
    (left right : List α) (hnonempty : slice.begin < slice.end) :
    MutSliceOwns (GF := GF) codec pool handle slice left ∗
        MutSliceOwns codec pool handle slice right ⊢ False := by
  have hbytes : 0 < (sliceRegion codec pool handle slice).bytes := by
    simp only [sliceRegion]
    exact Nat.mul_pos (Nat.sub_pos_of_lt hnonempty) codec.size_pos
  unfold MutSliceOwns
  iintro ⟨Hleft, Hright⟩
  icases Hleft with ⟨HleftRegion, _⟩
  icases Hright with ⟨HrightRegion, _⟩
  icombine HleftRegion HrightRegion as Hregions
  iapply ownsBytes_exclusive (sliceRegion codec pool handle slice) hbytes $$ Hregions

theorem mutSlice_split {GF : BundledGFunctors}
    [ByteRegionGS GF] [ByteContentsGS GF] {α : Type}
    (codec : Codec α) (pool : Region) (handle : Handle) (values : List α)
    (hlen : values.length = handle.len) (slice : SliceHandle)
    (hvalid : Valid codec handle) (hslice : SliceValid handle slice) :
    Owns (GF := GF) codec pool handle values ⊣⊢
      MutSliceOwns codec pool handle slice (sliceValues values slice) ∗
        MutSliceRest codec pool handle slice (values.take slice.begin)
          (values.drop slice.end) := by
  have hbegin : slice.begin ≤ slice.end := hslice.1
  have hend : slice.end ≤ values.length := by simpa [hlen] using hslice.2
  have hencoded := encodeValues_slice_decomposition codec values slice hbegin hend
  have hfit := sliceRegion_fits hvalid hslice
  let first := slice.begin * codec.size
  let middle := (slice.end - slice.begin) * codec.size
  let last := handle.block.bytes - (first + middle)
  have htotal : handle.block.bytes = first + middle + last := by
    dsimp [first, middle, last]
    omega
  have hendBytes : first + middle = slice.end * codec.size := by
    dsimp [first, middle]
    rw [← Nat.add_mul, Nat.add_sub_of_le hbegin]
  have hlast : last = handle.block.bytes - slice.end * codec.size := by
    simp [last, hendBytes]
  have hmiddleLength :
      (encodeValues codec (sliceValues values slice)).length = middle := by
    rw [encodeValues_length]
    have hsliceLength : (sliceValues values slice).length =
        slice.end - slice.begin := by
      simp [sliceValues, List.length_take, List.length_drop]
      omega
    rw [hsliceLength]
  have hprefixLength :
      (encodeValues codec (values.take slice.begin)).length = first := by
    rw [encodeValues_length, List.length_take,
      Nat.min_eq_left (Nat.le_trans hbegin hend)]
  have hregionSplit :
      OwnsBytes (PROP := IProp GF) (handle.block.region pool) ⊣⊢
        OwnsBytes (slicePrefixRegion codec pool handle slice) ∗
          (OwnsBytes (sliceRegion codec pool handle slice) ∗
            OwnsBytes (sliceTailRegion codec pool handle slice)) := by
    simpa [slicePrefixRegion, sliceRegion, sliceTailRegion, first, middle,
      hendBytes, hlast,
      Nat.add_sub_of_le hbegin, Nat.add_mul, Nat.add_assoc] using
      (ownsBytes_split3 (PROP := IProp GF) (handle.block.region pool)
        first middle last (by simpa [Block.region] using htotal))
  have hpointsSplit :
      PointsToBytes (G := (inferInstance : ByteContentsGS GF))
          (handle.block.region pool).base (encodeValues codec values) ⊣⊢
        PointsToBytes (handle.block.region pool).base
            (encodeValues codec (values.take slice.begin)) ∗
          (PointsToBytes (sliceRegion codec pool handle slice).base
              (encodeValues codec (sliceValues values slice)) ∗
            PointsToBytes ((handle.block.region pool).base +
                slice.end * codec.size)
              (encodeValues codec (values.drop slice.end))) := by
    rw [hencoded]
    have hsplit := (pointsToBytes_append (G :=
      (inferInstance : ByteContentsGS GF)) (handle.block.region pool).base
      (encodeValues codec (values.take slice.begin))
      (encodeValues codec (sliceValues values slice) ++
        encodeValues codec (values.drop slice.end))).trans
      (sep_congr_right (pointsToBytes_append
        ((handle.block.region pool).base +
          (encodeValues codec (values.take slice.begin)).length)
        (encodeValues codec (sliceValues values slice))
        (encodeValues codec (values.drop slice.end))))
    simpa [sliceRegion, hprefixLength, hmiddleLength, first, middle, hendBytes,
      Nat.add_sub_of_le hbegin, Nat.add_mul, Nat.add_assoc] using hsplit
  unfold Owns MutSliceOwns MutSliceRest
  constructor
  · iintro ⟨Hregion, Hpoints⟩
    ihave Hregions := hregionSplit.mp $$ Hregion
    icases Hregions with ⟨HprefixRegion, HmiddleAndTail⟩
    icases HmiddleAndTail with ⟨HmiddleRegion, HtailRegion⟩
    ihave Hpoints := hpointsSplit.mp $$ Hpoints
    icases Hpoints with ⟨HprefixPoints, HmiddleAndSuffix⟩
    icases HmiddleAndSuffix with ⟨HmiddlePoints, HsuffixPoints⟩
    isplitl [HmiddleRegion HmiddlePoints]
    · isplitl [HmiddleRegion]
      · iassumption
      · iassumption
    · isplitl [HprefixRegion HtailRegion]
      · isplitl [HprefixRegion]
        · iassumption
        · iassumption
      · isplitl [HprefixPoints]
        · iassumption
        · iassumption
  · iintro ⟨Hslice, Hrest⟩
    icases Hslice with ⟨HmiddleRegion, HmiddlePoints⟩
    icases Hrest with ⟨Hregions, Hpoints⟩
    icases Hregions with ⟨HprefixRegion, HtailRegion⟩
    icases Hpoints with ⟨HprefixPoints, HsuffixPoints⟩
    icombine HmiddlePoints HsuffixPoints as HmiddleAndSuffix
    icombine HprefixPoints HmiddleAndSuffix as HallPoints
    ihave HallPoints := hpointsSplit.mpr $$ HallPoints
    icombine HmiddleRegion HtailRegion as HmiddleAndTail
    icombine HprefixRegion HmiddleAndTail as HallRegions
    ihave HallRegions := hregionSplit.mpr $$ HallRegions
    isplitl [HallRegions]
    · iassumption
    · iassumption

theorem mutSlice_recombine {GF : BundledGFunctors}
    [ByteRegionGS GF] [ByteContentsGS GF] {α : Type}
    (codec : Codec α) (pool : Region) (handle : Handle) (slice : SliceHandle)
    (hvalid : Valid codec handle) (hslice : SliceValid handle slice)
    (prefixValues middleValues suffixValues : List α)
    (hprefix : prefixValues.length = slice.begin)
    (hmiddle : middleValues.length = slice.end - slice.begin)
    (_hlength : prefixValues.length + middleValues.length + suffixValues.length =
      handle.len) :
    MutSliceOwns (GF := GF) codec pool handle slice middleValues ∗
        MutSliceRest codec pool handle slice prefixValues suffixValues ⊢
      Owns codec pool handle (prefixValues ++ middleValues ++ suffixValues) := by
  have hbegin : slice.begin ≤ slice.end := hslice.1
  have hfit := sliceRegion_fits hvalid hslice
  let first := slice.begin * codec.size
  let middle := (slice.end - slice.begin) * codec.size
  let last := handle.block.bytes - (first + middle)
  have htotal : handle.block.bytes = first + middle + last := by
    dsimp [first, middle, last]
    omega
  have hendBytes : first + middle = slice.end * codec.size := by
    dsimp [first, middle]
    rw [← Nat.add_mul, Nat.add_sub_of_le hbegin]
  have hlast : last = handle.block.bytes - slice.end * codec.size := by
    simp [last, hendBytes]
  have hprefixLength : (encodeValues codec prefixValues).length = first := by
    rw [encodeValues_length, hprefix]
  have hmiddleLength : (encodeValues codec middleValues).length = middle := by
    rw [encodeValues_length, hmiddle]
  have hregionSplit :
      OwnsBytes (PROP := IProp GF) (handle.block.region pool) ⊣⊢
        OwnsBytes (slicePrefixRegion codec pool handle slice) ∗
          (OwnsBytes (sliceRegion codec pool handle slice) ∗
            OwnsBytes (sliceTailRegion codec pool handle slice)) := by
    simpa [slicePrefixRegion, sliceRegion, sliceTailRegion, first, middle,
      hendBytes, hlast, Nat.add_sub_of_le hbegin, Nat.add_mul,
      Nat.add_assoc] using
      (ownsBytes_split3 (PROP := IProp GF) (handle.block.region pool)
        first middle last (by simpa [Block.region] using htotal))
  have hpointsJoin :
      PointsToBytes (G := (inferInstance : ByteContentsGS GF))
          (handle.block.region pool).base (encodeValues codec prefixValues) ∗
        (PointsToBytes (sliceRegion codec pool handle slice).base
            (encodeValues codec middleValues) ∗
          PointsToBytes ((handle.block.region pool).base +
              slice.end * codec.size) (encodeValues codec suffixValues)) ⊢
      PointsToBytes (handle.block.region pool).base
        (encodeValues codec (prefixValues ++ middleValues ++ suffixValues)) := by
    have hsplit := (pointsToBytes_append (G :=
      (inferInstance : ByteContentsGS GF)) (handle.block.region pool).base
      (encodeValues codec prefixValues)
      (encodeValues codec middleValues ++ encodeValues codec suffixValues)).trans
      (sep_congr_right (pointsToBytes_append
        ((handle.block.region pool).base +
          (encodeValues codec prefixValues).length)
        (encodeValues codec middleValues) (encodeValues codec suffixValues)))
    rw [encodeValues_append, encodeValues_append]
    simpa [sliceRegion, hprefixLength, hmiddleLength, first, middle,
      hendBytes, Nat.add_assoc] using hsplit.mpr
  unfold MutSliceOwns MutSliceRest Owns
  iintro ⟨Hslice, Hrest⟩
  icases Hslice with ⟨HmiddleRegion, HmiddlePoints⟩
  icases Hrest with ⟨Hregions, Hpoints⟩
  icases Hregions with ⟨HprefixRegion, HtailRegion⟩
  icases Hpoints with ⟨HprefixPoints, HsuffixPoints⟩
  icombine HmiddlePoints HsuffixPoints as HmiddleAndSuffix
  icombine HprefixPoints HmiddleAndSuffix as HallPoints
  ihave HallPoints := hpointsJoin $$ HallPoints
  icombine HmiddleRegion HtailRegion as HmiddleAndTail
  icombine HprefixRegion HmiddleAndTail as HallRegions
  ihave HallRegions := hregionSplit.mpr $$ HallRegions
  isplitl [HallRegions]
  · iassumption
  · iassumption

theorem mutSlice_store {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {handle : Handle} {slice : SliceHandle}
    (oldValues newValues : List α) (hlength : oldValues.length = newValues.length)
    (contents : ContentsMap) (mem : Memory) (hrep : ContentsRep contents mem) :
    contentsInterp (G := G) contents ∗
        MutSliceOwns codec pool handle slice oldValues ==∗
      (contentsInterp
          (insertBytes contents (sliceRegion codec pool handle slice).base
            (encodeValues codec newValues)) ∗
        MutSliceOwns codec pool handle slice newValues) ∗
        ⌜∃ next, WriteSteps (sliceRegion codec pool handle slice).base
          (encodeValues codec newValues) mem next⌝ := by
  have hencodedLength : (encodeValues codec oldValues).length =
      (encodeValues codec newValues).length := by
    simp [encodeValues_length, hlength]
  unfold MutSliceOwns
  iintro ⟨Hcontents, Hslice⟩
  icases Hslice with ⟨Hregion, HoldPoints⟩
  icombine Hcontents HoldPoints as Hinitialized
  ihave ⟨Hinitialized, %hagreement⟩ := pointsToBytes_agreement contents
    (sliceRegion codec pool handle slice).base (encodeValues codec oldValues)
      $$ Hinitialized
  have hwrite : ∃ next, WriteSteps
      (sliceRegion codec pool handle slice).base
      (encodeValues codec newValues) mem next := by
    apply writeSteps_exists
    intro i hi
    have hiOld : i < (encodeValues codec oldValues).length := by
      rw [hencodedLength]
      exact hi
    let oldByte := (encodeValues codec oldValues)[i]
    have hget : (encodeValues codec oldValues)[i]? = some oldByte :=
      List.getElem?_eq_getElem hiOld
    have hmem := hrep ((sliceRegion codec pool handle slice).base + i) oldByte
      (hagreement i oldByte hget)
    unfold Memory.mapped
    simp [hmem]
  imod pointsToBytes_update contents
    (sliceRegion codec pool handle slice).base (encodeValues codec oldValues)
    (encodeValues codec newValues) hencodedLength $$ Hinitialized with
      ⟨Hcontents, HnewPoints⟩
  imodintro
  isplitl [Hcontents Hregion HnewPoints]
  · isplitl [Hcontents]
    · iassumption
    · isplitl [Hregion]
      · iassumption
      · iassumption
  · ipureintro
    exact hwrite

/-- Mutable-slice replacement returns the updated exclusive slice together
with a closed WP for the exact generated byte-store sequence. -/
theorem mutSlice_store_wp {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {handle : Handle} {slice : SliceHandle}
    (oldValues newValues : List α) (hlength : oldValues.length = newValues.length)
    (contents : ContentsMap) (mem : Memory) (hrep : ContentsRep contents mem) :
    contentsInterp (G := G) contents ∗
        MutSliceOwns codec pool handle slice oldValues ==∗
      (contentsInterp
          (insertBytes contents (sliceRegion codec pool handle slice).base
            (encodeValues codec newValues)) ∗
        MutSliceOwns codec pool handle slice newValues) ∗
        ⌜∃ next,
          WriteSteps (sliceRegion codec pool handle slice).base
            (encodeValues codec newValues) mem next ∧
          (⊢@{IProp GF} Program.wp
            (Program.writeBytes (sliceRegion codec pool handle slice).base
              (encodeValues codec newValues))
            mem (fun final => final = next))⌝ := by
  iintro H
  imod mutSlice_store codec oldValues newValues hlength contents mem hrep $$ H
    with ⟨H, %hwrite⟩
  imodintro
  isplitl [H]
  · iassumption
  · ipureintro
    obtain ⟨next, hsteps⟩ := hwrite
    exact ⟨next, hsteps, hsteps.program_wp⟩

theorem owns_empty {GF : BundledGFunctors}
    [ByteRegionGS GF] [ByteContentsGS GF] {α : Type}
    (codec : Codec α) (pool : Region) (handle : Handle) :
    Owns (GF := GF) codec pool handle [] ⊣⊢
      OwnsBytes (handle.block.region pool) := by
  simp only [Owns, encodeValues, List.flatMap_nil, PointsToBytes]
  exact sep_emp

theorem allocate_ownsFree {GF : BundledGFunctors}
    [ByteRegionGS GF] [ByteContentsGS GF] {α : Type}
    {codec : Codec α} {capacity : Nat} {hcapacity : 0 < capacity}
    {pool : Region} {state : Alloc.State}
    (hvalid : Alloc.Valid pool state)
    {hkeyMax : requestKey (allocationBytes codec capacity) <
      2 ^ firstLevelCount} {result : AllocResult}
    (hsuccess : allocate codec capacity hcapacity state hkeyMax = some result) :
    Ownership.OwnsFree (PROP := IProp GF) pool state.physical ⊣⊢
      Owns codec pool result.handle [] ∗
        Ownership.OwnsFree pool result.state.physical := by
  obtain ⟨raw, hraw, hhandle, hstate⟩ := allocate_result hsuccess
  rw [hhandle, hstate]
  have htransfer := Ownership.allocate_ownsFree (PROP := IProp GF)
    pool hvalid hraw
  simpa [Owns, encodeValues, PointsToBytes] using
    htransfer.trans (sep_congr_left sep_emp.symm)

def drop (pool : Region) (state : Alloc.State) (handle : Handle) :
    Option Alloc.State :=
  Box.drop pool state handle.block

theorem drop_preserves_valid {pool : Region} {state next : Alloc.State}
    (hvalid : Alloc.Valid pool state) {handle : Handle}
    (hsuccess : drop pool state handle = some next) : Alloc.Valid pool next :=
  Box.drop_preserves_valid hvalid hsuccess

theorem drop_complete {pool : Region} {state : Alloc.State}
    (hvalid : Alloc.Valid pool state)
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount) {handle : Handle}
    (hmember : handle.block ∈ state.physical)
    (hallocated : handle.block.free = false) :
    ∃ next, drop pool state handle = some next := by
  exact Box.drop_complete hvalid hpoolMax hmember (Bins.samePhysical_refl _)
    hallocated

theorem drop_owns {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {state next : Alloc.State}
    {handle : Handle} (values : List α) (contents : ContentsMap)
    (hdrop : drop pool state handle = some next) :
    contentsInterp (G := G) contents ∗
        (Owns codec pool handle values ∗
          Ownership.OwnsFree pool state.physical) ==∗
      contentsInterp (deleteBytes contents (handle.block.region pool).base
          (encodeValues codec values)) ∗
        Ownership.OwnsFree pool next.physical := by
  unfold drop at hdrop
  unfold Box.drop at hdrop
  cases hfind : Bins.findPhysicalIndex state.physical handle.block with
  | none => simp [hfind] at hdrop
  | some i =>
      have hdealloc : Dealloc.deallocate pool state i
          (handle.block.region pool) = some next := by
        simpa [hfind] using hdrop
      simp only [Owns]
      iintro ⟨Hcontents, Hrest⟩
      icases Hrest with ⟨Hvec, Hallocator⟩
      icases Hvec with ⟨Hregion, Hpoints⟩
      icombine Hcontents Hpoints as Hinitialized
      imod pointsToBytes_delete contents (handle.block.region pool).base
        (encodeValues codec values) $$ Hinitialized with Hcontents
      icombine Hregion Hallocator as Hreturn
      ihave Hallocator :=
        (Dealloc.deallocate_ownsFree (PROP := IProp GF) hdealloc).mp $$ Hreturn
      imodintro
      isplitl [Hcontents]
      · iassumption
      · iassumption

structure GrowResult where
  handle : Handle
  state : Alloc.State

/-- Allocate a replacement buffer and return the old buffer to TLSF. Byte
copying is specified separately by `grow_owns`; this pure transition changes
only allocator metadata. -/
def grow {α : Type} (codec : Codec α) (pool : Region) (handle : Handle)
    (newCapacity : Nat) (hcapacity : 0 < newCapacity) (state : Alloc.State)
    (hkeyMax : requestKey (allocationBytes codec newCapacity) <
      2 ^ firstLevelCount) : Option GrowResult :=
  match allocate codec newCapacity hcapacity state hkeyMax with
  | none => none
  | some allocated =>
      match drop pool allocated.state handle with
      | none => none
      | some next => some ⟨⟨allocated.handle.block, handle.len,
          newCapacity⟩, next⟩

theorem grow_result {α : Type} {codec : Codec α} {pool : Region}
    {handle : Handle} {newCapacity : Nat} {hcapacity : 0 < newCapacity}
    {state : Alloc.State}
    {hkeyMax : requestKey (allocationBytes codec newCapacity) <
      2 ^ firstLevelCount} {result : GrowResult}
    (hsuccess : grow codec pool handle newCapacity hcapacity state hkeyMax =
      some result) :
    ∃ allocated next,
      allocate codec newCapacity hcapacity state hkeyMax = some allocated ∧
      drop pool allocated.state handle = some next ∧
      result = ⟨⟨allocated.handle.block, handle.len, newCapacity⟩, next⟩ := by
  unfold grow at hsuccess
  cases halloc : allocate codec newCapacity hcapacity state hkeyMax with
  | none => simp [halloc] at hsuccess
  | some allocated =>
      cases hdrop : drop pool allocated.state handle with
      | none => simp [halloc, hdrop] at hsuccess
      | some next =>
          simp [halloc, hdrop] at hsuccess
          subst result
          exact ⟨allocated, next, rfl, hdrop, rfl⟩

theorem grow_preserves_valid {α : Type} {codec : Codec α} {pool : Region}
    {handle : Handle}
    {newCapacity : Nat} {hcapacity : 0 < newCapacity}
    (hlen : handle.len ≤ newCapacity) {state : Alloc.State}
    (hvalid : Alloc.Valid pool state)
    {hkeyMax : requestKey (allocationBytes codec newCapacity) <
      2 ^ firstLevelCount} {result : GrowResult}
    (hsuccess : grow codec pool handle newCapacity hcapacity state hkeyMax =
      some result) :
    Valid codec result.handle ∧ Alloc.Valid pool result.state := by
  obtain ⟨allocated, next, halloc, hdrop, rfl⟩ := grow_result hsuccess
  have hsafe := allocate_safe hvalid halloc
  have hnext := drop_preserves_valid hsafe.2.2.2 hdrop
  obtain ⟨raw, _, hallocated, _⟩ := allocate_result halloc
  have hcap : allocated.handle.capacity = newCapacity := by
    rw [hallocated]
  exact ⟨⟨hlen, by simpa [hcap] using hsafe.1.2⟩, hnext⟩

theorem grow_complete {α : Type} {codec : Codec α} {pool : Region}
    {handle : Handle} {newCapacity : Nat} {hcapacity : 0 < newCapacity}
    {state : Alloc.State} (hvalid : Alloc.Valid pool state)
    (hpoolMax : pool.bytes < 2 ^ firstLevelCount)
    (hmember : handle.block ∈ state.physical)
    (hallocated : handle.block.free = false)
    {hkeyMax : requestKey (allocationBytes codec newCapacity) <
      2 ^ firstLevelCount}
    (heligible : Bins.HasEligibleBin state.bins
      (searchSizeClass (allocationBytes codec newCapacity)
        (allocationBytes_positive codec hcapacity) hkeyMax)) :
    ∃ result,
      grow codec pool handle newCapacity hcapacity state hkeyMax = some result := by
  obtain ⟨allocated, halloc⟩ :=
    allocate_complete (hcapacity := hcapacity) hvalid heligible
  obtain ⟨raw, hraw, hhandle, hstate⟩ :=
    allocate_result (hcapacity := hcapacity) halloc
  have hnextValid :=
    (allocate_safe (hcapacity := hcapacity) hvalid halloc).2.2.2
  obtain ⟨updated, hupdated, hsame, _⟩ :=
    Alloc.allocate_preserves_allocated (hrequest :=
      allocationBytes_positive codec hcapacity) hvalid hraw hmember hallocated
  rw [hstate] at hnextValid
  obtain ⟨next, hdrop⟩ := Box.drop_complete hnextValid hpoolMax hupdated
    hsame hallocated
  exact ⟨⟨⟨allocated.handle.block, handle.len, newCapacity⟩, next⟩, by
    simp [grow, halloc, drop, hstate, hdrop]⟩

theorem replacement_regions_disjoint {α : Type} {codec : Codec α}
    {pool : Region} {handle : Handle} {newCapacity : Nat}
    {hcapacity : 0 < newCapacity} {state : Alloc.State}
    (hvalid : Alloc.Valid pool state) (hmember : handle.block ∈ state.physical)
    (hallocated : handle.block.free = false)
    {hkeyMax : requestKey (allocationBytes codec newCapacity) <
      2 ^ firstLevelCount} {allocated : AllocResult}
    (halloc : allocate codec newCapacity hcapacity state hkeyMax =
      some allocated) :
    (handle.block.region pool).disjoint
      (allocated.handle.block.region pool) := by
  obtain ⟨raw, hraw, hhandle, hstate⟩ :=
    allocate_result (hcapacity := hcapacity) halloc
  obtain ⟨updated, hupdated, hsame, hne⟩ :=
    Alloc.allocate_preserves_allocated (hrequest :=
      allocationBytes_positive codec hcapacity) hvalid hraw hmember hallocated
  have hnew : raw.allocated ∈ raw.state.physical :=
    Alloc.allocate_allocated_mem hraw
  have hnextValid :=
    (allocate_safe (hcapacity := hcapacity) hvalid halloc).2.2.2
  rw [hstate] at hnextValid
  have hdisjoint := wellFormed_regions_disjoint hnextValid.1 hupdated hnew hne
  have holdRegion := Bins.samePhysical_region hsame pool
  rw [← holdRegion, hhandle]
  exact hdisjoint

theorem grow_copy_steps {α : Type} {codec : Codec α} {pool : Region}
    {handle : Handle} (hhandle : Valid codec handle) {values : List α}
    (hlen : values.length = handle.len) {newCapacity : Nat}
    {hcapacity : 0 < newCapacity} (hlenCapacity : handle.len ≤ newCapacity)
    {state : Alloc.State} (hvalid : Alloc.Valid pool state)
    (hmember : handle.block ∈ state.physical)
    (hallocated : handle.block.free = false)
    {hkeyMax : requestKey (allocationBytes codec newCapacity) <
      2 ^ firstLevelCount} {allocated : AllocResult}
    (halloc : allocate codec newCapacity hcapacity state hkeyMax =
      some allocated) (mem : Memory)
    (hsrc : ∀ i value, (encodeValues codec values)[i]? = some value →
      mem ((handle.block.region pool).base + i) = some value)
    (hdst : ∀ i, i < (encodeValues codec values).length →
      mem.mapped ((allocated.handle.block.region pool).base + i)) :
    ∃ next, CopySteps (handle.block.region pool).base
      (allocated.handle.block.region pool).base (encodeValues codec values)
      mem next := by
  have hregions := replacement_regions_disjoint hvalid hmember hallocated halloc
  have holdFit : (encodeValues codec values).length ≤ handle.block.bytes := by
    rw [encodeValues_length, hlen]
    exact Nat.le_trans (Nat.mul_le_mul_right codec.size hhandle.1) hhandle.2
  have hnewSafe := (allocate_safe (hcapacity := hcapacity) hvalid halloc).1
  obtain ⟨raw, _, hnewHandle, _⟩ :=
    allocate_result (hcapacity := hcapacity) halloc
  have hnewFit : (encodeValues codec values).length ≤
      allocated.handle.block.bytes := by
    rw [encodeValues_length, hlen]
    have hcapBytes := Nat.mul_le_mul_right codec.size hlenCapacity
    have hcap : allocated.handle.capacity = newCapacity := by rw [hnewHandle]
    have hcapacityFit := hnewSafe.2
    rw [hcap] at hcapacityFit
    exact Nat.le_trans hcapBytes hcapacityFit
  apply copySteps_exists _ _ _ _ hsrc hdst
  intro i hi j hj heq
  have hiContains : (handle.block.region pool).contains
      ((handle.block.region pool).base + i) := by
    exact contains_offset _ _ (Nat.lt_of_lt_of_le hi holdFit)
  have hjContains : (allocated.handle.block.region pool).contains
      ((allocated.handle.block.region pool).base + j) := by
    exact contains_offset _ _ (Nat.lt_of_lt_of_le hj hnewFit)
  have hnot := not_contains_of_disjoint hregions hiContains
  apply hnot
  rw [heq]
  exact hjContains

theorem grow_owns_step {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {handle : Handle}
    {newCapacity : Nat} {hcapacity : 0 < newCapacity}
    {state : Alloc.State} (hvalid : Alloc.Valid pool state)
    {hkeyMax : requestKey (allocationBytes codec newCapacity) <
      2 ^ firstLevelCount} {allocated : AllocResult} {next : Alloc.State}
    (halloc : allocate codec newCapacity hcapacity state hkeyMax =
      some allocated)
    (hdrop : drop pool allocated.state handle = some next)
    (values : List α) (contents : ContentsMap)
    (hfresh : CanInsertBytes contents
      (allocated.handle.block.region pool).base (encodeValues codec values)) :
    contentsInterp (G := G) contents ∗
        (Owns codec pool handle values ∗
          Ownership.OwnsFree pool state.physical) ==∗
      contentsInterp
          (deleteBytes
            (insertBytes contents (allocated.handle.block.region pool).base
              (encodeValues codec values))
            (handle.block.region pool).base (encodeValues codec values)) ∗
        (Owns codec pool
            ⟨allocated.handle.block, handle.len, newCapacity⟩ values ∗
          Ownership.OwnsFree pool next.physical) := by
  iintro ⟨Hcontents, Hrest⟩
  icases Hrest with ⟨Hold, Hallocator⟩
  ihave Hallocated :=
    (allocate_ownsFree (GF := GF) hvalid halloc).mp $$ Hallocator
  icases Hallocated with ⟨Hempty, Hallocator⟩
  ihave HnewRegion := (owns_empty codec pool allocated.handle).mp $$ Hempty
  imod pointsToBytes_insert contents
    (allocated.handle.block.region pool).base (encodeValues codec values)
    hfresh $$ Hcontents with ⟨Hcontents, HnewPoints⟩
  icombine Hold Hallocator as HoldAndAllocator
  icombine Hcontents HoldAndAllocator as HdropInput
  imod drop_owns codec values
    (insertBytes contents (allocated.handle.block.region pool).base
      (encodeValues codec values)) hdrop $$ HdropInput with
    ⟨Hcontents, Hallocator⟩
  imodintro
  isplitl [Hcontents]
  · iassumption
  · isplitr [Hallocator]
    · unfold Owns
      isplitl [HnewRegion]
      · iassumption
      · iassumption
    · iassumption

/-- Exact Vec ownership exposes authoritative agreement for its initialized
prefix without consuming either the Vec or the authoritative map. -/
theorem owns_agreement {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) (pool : Region) (handle : Handle) (values : List α)
    (contents : ContentsMap) :
    contentsInterp (G := G) contents ∗ Owns codec pool handle values ⊢
      (contentsInterp contents ∗ Owns codec pool handle values) ∗
        ⌜BytesInContents contents (handle.block.region pool).base
          (encodeValues codec values)⌝ := by
  unfold Owns
  iintro ⟨Hcontents, Howns⟩
  icases Howns with ⟨Hregion, Hpoints⟩
  icombine Hcontents Hpoints as Hagreement
  ihave ⟨Hagreement, %hbytes⟩ := pointsToBytes_agreement contents
    (handle.block.region pool).base (encodeValues codec values) $$ Hagreement
  icases Hagreement with ⟨Hcontents, Hpoints⟩
  isplitl [Hcontents Hregion Hpoints]
  · isplitl [Hcontents]
    · iassumption
    · isplitl [Hregion]
      · iassumption
      · iassumption
  · ipureintro
    exact hbytes

/-- Framed growth rule with the operational byte-copy witness. Agreement with
the authoritative content map supplies every source load; allocation validity
supplies non-overlap, and mapped replacement bytes supply every destination
store. The ownership update and execution trace describe the same encoding. -/
theorem grow_owns_step_with_copy {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {handle : Handle}
    (hhandle : Valid codec handle) {newCapacity : Nat}
    {hcapacity : 0 < newCapacity} (hlenCapacity : handle.len ≤ newCapacity)
    {state : Alloc.State} (hvalid : Alloc.Valid pool state)
    (hmember : handle.block ∈ state.physical)
    (hallocated : handle.block.free = false)
    {hkeyMax : requestKey (allocationBytes codec newCapacity) <
      2 ^ firstLevelCount} {allocated : AllocResult} {next : Alloc.State}
    (halloc : allocate codec newCapacity hcapacity state hkeyMax =
      some allocated)
    (hdrop : drop pool allocated.state handle = some next)
    (values : List α) (hlen : values.length = handle.len)
    (contents : ContentsMap) (mem : Memory) (hrep : ContentsRep contents mem)
    (hdst : ∀ i, i < (encodeValues codec values).length →
      mem.mapped ((allocated.handle.block.region pool).base + i))
    (hfresh : CanInsertBytes contents
      (allocated.handle.block.region pool).base (encodeValues codec values)) :
    contentsInterp (G := G) contents ∗
        (Owns codec pool handle values ∗
          Ownership.OwnsFree pool state.physical) ==∗
      (contentsInterp
          (deleteBytes
            (insertBytes contents (allocated.handle.block.region pool).base
              (encodeValues codec values))
            (handle.block.region pool).base (encodeValues codec values)) ∗
        (Owns codec pool
            ⟨allocated.handle.block, handle.len, newCapacity⟩ values ∗
          Ownership.OwnsFree pool next.physical)) ∗
        ⌜∃ memNext, CopySteps (handle.block.region pool).base
          (allocated.handle.block.region pool).base
          (encodeValues codec values) mem memNext⌝ := by
  iintro ⟨Hcontents, Hrest⟩
  icases Hrest with ⟨Hold, Hallocator⟩
  icombine Hcontents Hold as Hagreement
  ihave ⟨Hagreement, %hbytes⟩ := owns_agreement codec pool handle values
    contents $$ Hagreement
  icases Hagreement with ⟨Hcontents, Hold⟩
  have hsrc : ∀ i value, (encodeValues codec values)[i]? = some value →
      mem ((handle.block.region pool).base + i) = some value := by
    intro i value hget
    exact hrep _ _ (hbytes i value hget)
  obtain ⟨memNext, hcopy⟩ := grow_copy_steps hhandle hlen hlenCapacity hvalid
    hmember hallocated halloc mem hsrc hdst
  isplitl [Hcontents Hold Hallocator]
  ·
    icombine Hold Hallocator as Hrest
    icombine Hcontents Hrest as Hinput
    iapply grow_owns_step codec hvalid halloc hdrop values contents hfresh $$ Hinput
  · ipureintro
    exact ⟨memNext, hcopy⟩

/-- Whole-program counterpart of `grow_owns_step_with_copy`: the relocation
trace is also a semantic WP for the generated byte-copy program. Thus Vec
growth does not stop at exhibiting individual safe accesses; it supplies the
closed no-stuck program proof consumed by adequacy. -/
theorem grow_owns_step_with_copy_wp {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {handle : Handle}
    (hhandle : Valid codec handle) {newCapacity : Nat}
    {hcapacity : 0 < newCapacity} (hlenCapacity : handle.len ≤ newCapacity)
    {state : Alloc.State} (hvalid : Alloc.Valid pool state)
    (hmember : handle.block ∈ state.physical)
    (hallocated : handle.block.free = false)
    {hkeyMax : requestKey (allocationBytes codec newCapacity) <
      2 ^ firstLevelCount} {allocated : AllocResult} {next : Alloc.State}
    (halloc : allocate codec newCapacity hcapacity state hkeyMax =
      some allocated)
    (hdrop : drop pool allocated.state handle = some next)
    (values : List α) (hlen : values.length = handle.len)
    (contents : ContentsMap) (mem : Memory) (hrep : ContentsRep contents mem)
    (hdst : ∀ i, i < (encodeValues codec values).length →
      mem.mapped ((allocated.handle.block.region pool).base + i))
    (hfresh : CanInsertBytes contents
      (allocated.handle.block.region pool).base (encodeValues codec values)) :
    contentsInterp (G := G) contents ∗
        (Owns codec pool handle values ∗
          Ownership.OwnsFree pool state.physical) ==∗
      (contentsInterp
          (deleteBytes
            (insertBytes contents (allocated.handle.block.region pool).base
              (encodeValues codec values))
            (handle.block.region pool).base (encodeValues codec values)) ∗
        (Owns codec pool
            ⟨allocated.handle.block, handle.len, newCapacity⟩ values ∗
          Ownership.OwnsFree pool next.physical)) ∗
        ⌜∃ memNext,
          CopySteps (handle.block.region pool).base
            (allocated.handle.block.region pool).base
            (encodeValues codec values) mem memNext ∧
          (⊢@{IProp GF} Program.wp
            (Program.copyBytes (handle.block.region pool).base
              (allocated.handle.block.region pool).base
              (encodeValues codec values)) mem
            (fun final => final = memNext)) ∧
          (⊢@{IProp GF} Program.wp
            (Program.copyLoop (handle.block.region pool).base
              (allocated.handle.block.region pool).base
              (encodeValues codec values).length) mem
            (fun final => final = memNext))⌝ := by
  iintro H
  imod grow_owns_step_with_copy codec hhandle hlenCapacity hvalid hmember
    hallocated halloc hdrop values hlen contents mem hrep hdst hfresh $$ H with H
  icases H with ⟨Hresources, %htrace⟩
  obtain ⟨memNext, hsteps⟩ := htrace
  isplitl [Hresources]
  · iassumption
  · ipureintro
    exact ⟨memNext, hsteps, hsteps.program_wp, hsteps.copyLoop_wp_exact⟩

theorem owns_exclusive {GF : BundledGFunctors}
    [ByteRegionGS GF] [ByteContentsGS GF] {α : Type}
    (codec : Codec α) (pool : Region) (handle : Handle)
    (left right : List α) (hbytes : 0 < handle.block.bytes) :
    Owns (GF := GF) codec pool handle left ∗ Owns codec pool handle right ⊢
      False := by
  unfold Owns
  iintro ⟨Hleft, Hright⟩
  icases Hleft with ⟨HleftBytes, _⟩
  icases Hright with ⟨HrightBytes, _⟩
  icombine HleftBytes HrightBytes as H
  iapply ownsBytes_exclusive (handle.block.region pool) hbytes $$ H

theorem index_fits {α : Type} {codec : Codec α} {handle : Handle}
    (hvalid : Valid codec handle) {values : List α}
    (_hlen : values.length = handle.len) {i : Nat} (hi : i < handle.len) :
    i * codec.size + codec.size ≤ handle.block.bytes := by
  rcases hvalid with ⟨hlenCap, hcapacity⟩
  have hindex : i + 1 ≤ handle.capacity := by omega
  have := Nat.mul_le_mul_right codec.size hindex
  rw [Nat.add_mul] at this
  simpa using Nat.le_trans this hcapacity

theorem index_flat_lt {α : Type} (codec : Codec α) {handle : Handle}
    {values : List α} (hlen : values.length = handle.len)
    {i byteIndex : Nat} (hi : i < handle.len)
    (hbyte : byteIndex < codec.size) :
    i * codec.size + byteIndex < (encodeValues codec values).length := by
  rw [encodeValues_length, hlen]
  have hnext : i + 1 ≤ handle.len := by omega
  have hlocal : i * codec.size + byteIndex < (i + 1) * codec.size := by
    rw [Nat.add_mul]
    omega
  have hcapacity := Nat.mul_le_mul_right codec.size hnext
  exact Nat.lt_of_lt_of_le hlocal hcapacity

theorem index_byte {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {handle : Handle} {values : List α}
    (hlen : values.length = handle.len) {contents : ContentsMap} {mem : Memory}
    (hrep : ContentsRep contents mem) {i byteIndex : Nat}
    (hi : i < handle.len) (hbyte : byteIndex < codec.size) :
    contentsInterp (G := G) contents ∗ Owns codec pool handle values ⊢
      ⌜PrimStep (.load ((handle.block.region pool).base +
          (i * codec.size + byteIndex))) mem
        (.byte ((encodeValues codec values).get
          ⟨i * codec.size + byteIndex,
            index_flat_lt codec hlen hi hbyte⟩)) mem⌝ := by
  simp only [Owns]
  iintro ⟨Hcontents, Hvec⟩
  icases Hvec with ⟨_, Hpoints⟩
  icombine Hcontents Hpoints as H
  have hflat := index_flat_lt codec hlen hi hbyte
  iapply pointsToBytes_load_exact hrep hflat $$ H

theorem read_initialized_prefix {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {handle : Handle} {values : List α}
    {contents : ContentsMap} {mem : Memory} (hrep : ContentsRep contents mem) :
    contentsInterp (G := G) contents ∗ Owns codec pool handle values ⊢
      (contentsInterp contents ∗ Owns codec pool handle values) ∗
        ⌜ReadSteps (handle.block.region pool).base
          (encodeValues codec values) mem ∧
          ∀ value ∈ values, codec.decode (codec.encode value) = some value⌝ := by
  simp only [Owns]
  iintro ⟨Hcontents, Hvec⟩
  icases Hvec with ⟨Hregion, Hpoints⟩
  icombine Hcontents Hpoints as Hread
  ihave ⟨Hread, %hsteps⟩ := pointsToBytes_read_steps hrep
    (handle.block.region pool).base (encodeValues codec values) $$ Hread
  icases Hread with ⟨Hcontents, Hpoints⟩
  isplitl [Hcontents Hregion Hpoints]
  · isplitl [Hcontents]
    · iassumption
    · isplitl [Hregion]
      · iassumption
      · iassumption
  · ipureintro
    exact ⟨hsteps, fun value _ => codec.decode_encode value⟩

/-- The complete initialized Vec prefix is a compositional generated-effect
program with a closed no-stuck WP, while the typed Vec capability is retained. -/
theorem read_initialized_prefix_wp {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {handle : Handle} {values : List α}
    {contents : ContentsMap} {mem : Memory} (hrep : ContentsRep contents mem) :
    contentsInterp (G := G) contents ∗ Owns codec pool handle values ⊢
      (contentsInterp contents ∗ Owns codec pool handle values) ∗
        Program.wp
          (Program.readBytes (handle.block.region pool).base
            (encodeValues codec values).length)
          mem (fun final => final = mem) := by
  iintro H
  ihave ⟨H, %hread⟩ := read_initialized_prefix codec hrep $$ H
  isplitl [H]
  · iassumption
  · exact hread.1.program_wp

theorem read_element {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {handle : Handle} {values : List α}
    (hlen : values.length = handle.len) {contents : ContentsMap} {mem : Memory}
    (hrep : ContentsRep contents mem) {i : Nat} (hi : i < handle.len) :
    contentsInterp (G := G) contents ∗ Owns codec pool handle values ⊢
      (contentsInterp contents ∗ Owns codec pool handle values) ∗
        ⌜ReadSteps ((handle.block.region pool).base + i * codec.size)
            (codec.encode values[i]) mem ∧
          codec.decode (codec.encode values[i]) = some values[i]⌝ := by
  have hiValues : i < values.length := by simpa [hlen] using hi
  have hsplit := encodeValues_split_at codec values hiValues
  have hprefixLength : (encodeValues codec (values.take i)).length =
      i * codec.size := by
    rw [encodeValues_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hiValues)]
  simp only [Owns]
  rw [hsplit]
  iintro ⟨Hcontents, Hvec⟩
  icases Hvec with ⟨Hregion, Hpoints⟩
  ihave Hsplit := (pointsToBytes_append (handle.block.region pool).base
    (encodeValues codec (values.take i))
    (codec.encode values[i] ++ encodeValues codec (values.drop (i + 1)))).mp
      $$ Hpoints
  icases Hsplit with ⟨Hprefix, Hrest⟩
  ihave Hsplit := (pointsToBytes_append
    ((handle.block.region pool).base +
      (encodeValues codec (values.take i)).length)
    (codec.encode values[i])
    (encodeValues codec (values.drop (i + 1)))).mp $$ Hrest
  icases Hsplit with ⟨Helement, Hsuffix⟩
  icombine Hcontents Helement as Hread
  ihave ⟨Hread, %hsteps⟩ := pointsToBytes_read_steps hrep
    ((handle.block.region pool).base +
      (encodeValues codec (values.take i)).length)
    (codec.encode values[i]) $$ Hread
  icases Hread with ⟨Hcontents, Helement⟩
  rw [hprefixLength] at hsteps
  icombine Helement Hsuffix as Hrest
  ihave Hrest := (pointsToBytes_append
    ((handle.block.region pool).base +
      (encodeValues codec (values.take i)).length)
    (codec.encode values[i])
    (encodeValues codec (values.drop (i + 1)))).mpr $$ Hrest
  icombine Hprefix Hrest as Hpoints
  ihave Hpoints := (pointsToBytes_append (handle.block.region pool).base
    (encodeValues codec (values.take i))
    (codec.encode values[i] ++ encodeValues codec (values.drop (i + 1)))).mpr
      $$ Hpoints
  isplitl [Hcontents Hregion Hpoints]
  · isplitl [Hcontents]
    · iassumption
    · isplitl [Hregion]
      · iassumption
      · iassumption
  · ipureintro
    exact ⟨hsteps, codec.decode_encode values[i]⟩

theorem read_slice {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {handle : Handle} {values : List α}
    (hlen : values.length = handle.len) {slice : SliceHandle}
    (hslice : SliceValid handle slice) {contents : ContentsMap} {mem : Memory}
    (hrep : ContentsRep contents mem) :
    contentsInterp (G := G) contents ∗ Owns codec pool handle values ⊢
      (contentsInterp contents ∗ Owns codec pool handle values) ∗
        ⌜ReadSteps (sliceRegion codec pool handle slice).base
            (encodeValues codec (sliceValues values slice)) mem ∧
          ∀ value ∈ sliceValues values slice,
            codec.decode (codec.encode value) = some value⌝ := by
  have hbegin : slice.begin ≤ slice.end := hslice.1
  have hend : slice.end ≤ values.length := by simpa [hlen] using hslice.2
  have hsplit := encodeValues_slice_decomposition codec values slice hbegin hend
  have hprefixLength :
      (encodeValues codec (values.take slice.begin)).length =
        slice.begin * codec.size := by
    rw [encodeValues_length, List.length_take,
      Nat.min_eq_left (Nat.le_trans hbegin hend)]
  simp only [Owns]
  rw [hsplit]
  iintro ⟨Hcontents, Hvec⟩
  icases Hvec with ⟨Hregion, Hpoints⟩
  ihave Hsplit := (pointsToBytes_append (handle.block.region pool).base
    (encodeValues codec (values.take slice.begin))
    (encodeValues codec (sliceValues values slice) ++
      encodeValues codec (values.drop slice.end))).mp $$ Hpoints
  icases Hsplit with ⟨Hprefix, Hrest⟩
  ihave Hsplit := (pointsToBytes_append
    ((handle.block.region pool).base +
      (encodeValues codec (values.take slice.begin)).length)
    (encodeValues codec (sliceValues values slice))
    (encodeValues codec (values.drop slice.end))).mp $$ Hrest
  icases Hsplit with ⟨Hmiddle, Hsuffix⟩
  icombine Hcontents Hmiddle as Hread
  ihave ⟨Hread, %hsteps⟩ := pointsToBytes_read_steps hrep
    ((handle.block.region pool).base +
      (encodeValues codec (values.take slice.begin)).length)
    (encodeValues codec (sliceValues values slice)) $$ Hread
  icases Hread with ⟨Hcontents, Hmiddle⟩
  have hbase : (sliceRegion codec pool handle slice).base =
      (handle.block.region pool).base +
        (encodeValues codec (values.take slice.begin)).length := by
    simp [sliceRegion, hprefixLength]
  rw [← hbase] at hsteps
  icombine Hmiddle Hsuffix as Hrest
  ihave Hrest := (pointsToBytes_append
    ((handle.block.region pool).base +
      (encodeValues codec (values.take slice.begin)).length)
    (encodeValues codec (sliceValues values slice))
    (encodeValues codec (values.drop slice.end))).mpr $$ Hrest
  icombine Hprefix Hrest as Hpoints
  ihave Hpoints := (pointsToBytes_append (handle.block.region pool).base
    (encodeValues codec (values.take slice.begin))
    (encodeValues codec (sliceValues values slice) ++
      encodeValues codec (values.drop slice.end))).mpr $$ Hpoints
  isplitl [Hcontents Hregion Hpoints]
  · isplitl [Hcontents]
    · iassumption
    · isplitl [Hregion]
      · iassumption
      · iassumption
  · ipureintro
    exact ⟨hsteps, fun value _ => codec.decode_encode value⟩

theorem push_owns {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {handle next : Handle}
    {values : List α} (value : α) (contents : ContentsMap)
    (hsuccess : push handle = some next)
    (hfresh : CanInsertBytes contents
      ((handle.block.region pool).base + (encodeValues codec values).length)
      (codec.encode value)) :
    contentsInterp (G := G) contents ∗ Owns codec pool handle values ==∗
      contentsInterp (insertBytes contents
          ((handle.block.region pool).base + (encodeValues codec values).length)
          (codec.encode value)) ∗
        Owns codec pool next (values ++ [value]) := by
  obtain ⟨_, rfl⟩ := push_result hsuccess
  have hencoded : encodeValues codec (values ++ [value]) =
      encodeValues codec values ++ codec.encode value := by
    simp [encodeValues]
  simp only [Owns]
  iintro ⟨Hcontents, Hvec⟩
  icases Hvec with ⟨Hregion, Hold⟩
  imod pointsToBytes_insert contents
    ((handle.block.region pool).base + (encodeValues codec values).length)
    (codec.encode value) hfresh $$ Hcontents with ⟨Hcontents, Hnew⟩
  icombine Hold Hnew as Hpoints
  ihave Hpoints := (pointsToBytes_append
    (handle.block.region pool).base (encodeValues codec values)
      (codec.encode value)).mpr $$ Hpoints
  imodintro
  isplitl [Hcontents]
  · iassumption
  · isplitl [Hregion]
    · iassumption
    · rw [hencoded]
      iassumption

/-- Push into spare capacity is operationally safe even though those bytes
were not previously initialized in the contents map. Allocation ownership and
`MemoryRep` prove the complete encoded destination mapped; the content update
then establishes the extended typed Vec ownership. -/
theorem push_owns_wp {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {handle next : Handle}
    {values : List α} (value : α) (contents : ContentsMap)
    {allocated : ByteMap Unit} {mem : Memory}
    (hvalid : Valid codec handle) (hlen : values.length = handle.len)
    (hrep : MemoryRep allocated mem)
    (hsuccess : push handle = some next)
    (hfresh : CanInsertBytes contents
      ((handle.block.region pool).base + (encodeValues codec values).length)
      (codec.encode value)) :
    byteHeapInterp (G := (inferInstance : ByteRegionGS GF)) allocated ∗
        (contentsInterp (G := G) contents ∗ Owns codec pool handle values) ==∗
      byteHeapInterp allocated ∗
        (contentsInterp (insertBytes contents
            ((handle.block.region pool).base +
              (encodeValues codec values).length)
            (codec.encode value)) ∗
          Owns codec pool next (values ++ [value])) ∗
        ⌜∃ memNext,
          WriteSteps
            ((handle.block.region pool).base +
              (encodeValues codec values).length)
            (codec.encode value) mem memNext ∧
          (⊢@{IProp GF} Program.wp
            (Program.writeBytes
              ((handle.block.region pool).base +
                (encodeValues codec values).length)
              (codec.encode value))
            mem (fun final => final = memNext))⌝ := by
  obtain ⟨hlt, rfl⟩ := push_result hsuccess
  have hencoded : encodeValues codec (values ++ [value]) =
      encodeValues codec values ++ codec.encode value := by
    simp [encodeValues]
  have hinside : ∀ i, i < (codec.encode value).length →
      (handle.block.region pool).contains
        ((handle.block.region pool).base +
          (encodeValues codec values).length + i) := by
    intro i hi
    have hiSize : i < codec.size := by
      simpa [codec.encode_length] using hi
    have hnextCapacity : handle.len + 1 ≤ handle.capacity := by omega
    have hnextBytes : (handle.len + 1) * codec.size ≤
        handle.capacity * codec.size :=
      Nat.mul_le_mul_right codec.size hnextCapacity
    have hoffset : handle.len * codec.size + i < handle.block.bytes := by
      rcases hvalid with ⟨_, hcapacityBytes⟩
      rw [Nat.add_mul] at hnextBytes
      omega
    have hcontains := contains_offset (handle.block.region pool)
      (handle.len * codec.size + i) hoffset
    simpa [encodeValues_length, hlen, Nat.add_assoc] using hcontains
  simp only [Owns]
  iintro ⟨Hheap, Hcontainer⟩
  icases Hcontainer with ⟨Hcontents, Hvec⟩
  icases Hvec with ⟨Hregion, Hpoints⟩
  icombine Hheap Hregion as Hmapped
  ihave %hwrite := owned_writeBytes_wp (G := (inferInstance : ByteRegionGS GF))
    (codec.encode value) hrep hinside $$ Hmapped
  icases Hmapped with ⟨Hheap, Hregion⟩
  imod pointsToBytes_insert contents
    ((handle.block.region pool).base + (encodeValues codec values).length)
    (codec.encode value) hfresh $$ Hcontents with ⟨Hcontents, Hnew⟩
  icombine Hpoints Hnew as Hpoints
  ihave Hpoints := (pointsToBytes_append
    (handle.block.region pool).base (encodeValues codec values)
      (codec.encode value)).mpr $$ Hpoints
  imodintro
  isplitl [Hheap]
  · iassumption
  · isplitl [Hcontents Hregion Hpoints]
    · isplitl [Hcontents]
      · iassumption
      · isplitl [Hregion]
        · iassumption
        · rw [hencoded]
          iassumption
    · ipureintro
      exact hwrite

theorem pop_owns {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {handle next : Handle}
    (initValues : List α) (last : α) (contents : ContentsMap)
    (hlen : handle.len = initValues.length + 1)
    (hsuccess : pop handle = some next) :
    contentsInterp (G := G) contents ∗
        Owns codec pool handle (initValues ++ [last]) ==∗
      contentsInterp (deleteBytes contents
          ((handle.block.region pool).base +
            (encodeValues codec initValues).length)
          (codec.encode last)) ∗
        (⌜next.len = initValues.length⌝ ∗ Owns codec pool next initValues) := by
  obtain ⟨_, hnext⟩ := pop_result hsuccess
  subst next
  have hencoded : encodeValues codec (initValues ++ [last]) =
      encodeValues codec initValues ++ codec.encode last := by
    simp [encodeValues]
  simp only [Owns]
  rw [hencoded]
  iintro ⟨Hcontents, Hvec⟩
  icases Hvec with ⟨Hregion, Hpoints⟩
  ihave Hsplit := (pointsToBytes_append
    (handle.block.region pool).base (encodeValues codec initValues)
      (codec.encode last)).mp $$ Hpoints
  icases Hsplit with ⟨Hprefix, Hlast⟩
  icombine Hcontents Hlast as Hdelete
  imod pointsToBytes_delete contents
    ((handle.block.region pool).base + (encodeValues codec initValues).length)
    (codec.encode last) $$ Hdelete with Hcontents
  imodintro
  isplitl [Hcontents]
  · iassumption
  · isplit
    · ipureintro
      simp [hlen]
    · isplitl [Hregion]
      · iassumption
      · iassumption

/-- A generic Vec pop reads exactly the final initialized encoding before
removing it from the logical contents map. The returned value is fixed by the
codec round trip, the shortened Vec retains the sole allocation capability,
and the exact generated read program has a closed no-stuck WP. -/
theorem pop_owns_wp {GF : BundledGFunctors}
    [ByteRegionGS GF] [G : ByteContentsGS GF] {α : Type}
    (codec : Codec α) {pool : Region} {handle next : Handle}
    (initValues : List α) (last : α) (contents : ContentsMap)
    {mem : Memory} (hrep : ContentsRep contents mem)
    (hlen : handle.len = initValues.length + 1)
    (hsuccess : pop handle = some next) :
    contentsInterp (G := G) contents ∗
        Owns codec pool handle (initValues ++ [last]) ==∗
      (contentsInterp (deleteBytes contents
          ((handle.block.region pool).base +
            (encodeValues codec initValues).length)
          (codec.encode last)) ∗
        (⌜next.len = initValues.length⌝ ∗ Owns codec pool next initValues)) ∗
        ⌜ReadSteps
            ((handle.block.region pool).base + initValues.length * codec.size)
            (codec.encode last) mem ∧
          codec.decode (codec.encode last) = some last ∧
          (⊢@{IProp GF} Program.wp
            (Program.readBytes
              ((handle.block.region pool).base +
                initValues.length * codec.size)
              codec.size)
            mem (fun final => final = mem))⌝ := by
  have hvaluesLen : (initValues ++ [last]).length = handle.len := by
    simp [hlen]
  have hlast : initValues.length < handle.len := by omega
  iintro H
  ihave ⟨H, %hread⟩ := read_element codec hvaluesLen hrep hlast $$ H
  imod pop_owns codec initValues last contents hlen hsuccess $$ H with H
  isplitl [H]
  · iassumption
  · ipureintro
    have hindex : (initValues ++ [last])[initValues.length] = last := by simp
    rw [hindex] at hread
    exact ⟨hread.1, hread.2, by
      simpa [codec.encode_length] using hread.1.program_wp⟩

end Luffs.Containers.Vec
