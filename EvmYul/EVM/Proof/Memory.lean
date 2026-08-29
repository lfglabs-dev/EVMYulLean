import EvmYul.MachineStateOps

/-! # Memory read-over-write

`MachineState.memory` is a flat `ByteArray`, written through `ByteArray.write`
and read back through `ByteArray.readWithPadding`. Both are defined for the
interpreter rather than for proofs: `write` splices with `copySlice` after
zero-padding both operands to cover out-of-range offsets, and `readWithPadding`
clamps its length and then re-pads. Neither reduces on its own, so a proof that
wants to know what a `MSTORE` left in memory has nothing to appeal to.

This file supplies the missing equations, in three layers.

* `ByteArray.write_eq_of_fits` is the normal form: when the written span lies
  inside the destination, every padding term in `write` collapses and the result
  is the plain three-way splice `dest[0, a) ++ src ++ dest[a + len, size)`.
  `ByteArray.readWithPadding_eq_extract` is the matching normal form for the
  read side, where the padding is likewise empty.
* `ByteArray.write_eq_of_grows` is the normal form for the *other* branch, the
  one a write past the end of memory takes: `write` zero-extends the destination
  itself, so the result is `dest[0, destAddr) ++ 0…0 ++ src` and memory ends up
  `max dest.size (destAddr + len)` long (`ByteArray.size_write`).
* `ByteArray.readWithPadding_write_self` is read-over-write proper: reading back
  exactly the span that was just written returns the source.
  `readWithPadding_write_self_of_pad` is the same statement with no hypothesis
  about `dest.size` at all, by combining the two branches. Its two companions
  `readWithPadding_write_of_le` and `readWithPadding_write_of_ge` are the frame
  half — a read disjoint from the written span does not see the write.
* The `MachineState` layer specialises these to the operations the semantics
  actually dispatches on: `readWithPadding_memory_mstore8`,
  `readWithPadding_memory_mstore`, and `H_return_evmReturn_mstore`, which is the
  composite a `MSTORE`-then-`RETURN` fragment needs — the bytes a contract
  returns are the word it stored. Each has an `_of_le` variant that drops the
  in-bounds hypothesis, and `H_return_evmReturn_mstore_zero` drops it entirely.

Everything rests on `EvmYul.MachineStateOps` and the Lean core `ByteArray`
lemmas. No axiom is introduced and no proof is admitted.

## For consumers

`import EvmYul.EVM.Proof.Memory`. A proof that has to discharge a goal of the
shape `μ.memory.readWithPadding a l = …` wants, in rough order of usefulness:

| Goal shape | Lemma |
| --- | --- |
| `MSTORE(0, v)`; `RETURN(0, 32)` returns `v` | `EvmYul.MachineState.H_return_evmReturn_mstore_zero` |
| bytes returned after `MSTORE`; `RETURN` | `EvmYul.MachineState.H_return_evmReturn_mstore_of_le` |
| `H_return` of an `evmReturn` | `EvmYul.MachineState.H_return_evmReturn` |
| read back an `MSTORE`d word | `EvmYul.MachineState.readWithPadding_memory_mstore_of_le` |
| read back an `MSTORE8`d byte | `EvmYul.MachineState.readWithPadding_memory_mstore8_of_le` |
| `spos + 32` is in bounds after the store | `EvmYul.MachineState.le_size_memory_mstore` |
| memory size across a store | `EvmYul.MachineState.size_memory_mstore_of_pad` |
| read disjoint from a store | `ByteArray.readWithPadding_write_of_le` / `_of_ge` |
| generic read-over-write | `ByteArray.readWithPadding_write_self_of_pad` |
| unfold `write` / `readWithPadding` | `ByteArray.write_eq_of_fits` / `_of_grows` / `readWithPadding_eq_extract` |

`EvmYul.UInt256.size_toByteArray` (a stored word is exactly 32 bytes) is the
side condition most of the `MSTORE` lemmas need supplied at their call sites.

## Where the in-bounds hypotheses come from

`write` and `readWithPadding` genuinely behave differently when a span runs past
the end of memory — `readWithoutPadding` clamps with `min len source.size`, which
is the *total* size rather than the remaining size — so the `_of_fits` equations
really do need their hypotheses.

What supplies them is **the store, not the gas charge**. `MachineState.M` feeds
`activeWords` and provably leaves `memory` alone
(`MachineState.memory_activeWords_update`), so a frame that has charged expansion
for `[0, 32)` still has `memory.size = 0` and cannot satisfy
`spos.toNat + 32 ≤ μ.memory.size`. Frames start empty, so this is not a corner
case: it is what the canonical `MSTORE(0, v); RETURN(0, 32)` fragment looks like.

`write` closes the gap on its own, by zero-extending its destination. Hence
`le_size_memory_mstore`: `spos + 32 ≤ (μ.mstore spos sval).memory.size`, with no
assumption on `μ`. The `_of_le` and `_zero` lemmas are the read-side consequences,
and they are the ones to cite; the `_of_fits` originals are kept because they are
true and are the cheaper rewrite when a caller does already know the span fits.

The one residual side condition is `_of_pad`: `destAddr - dest.size` must not
wrap `USize`. Above that gap the zero-padding length really does wrap and the
write really does land elsewhere, so the hypothesis is load-bearing rather than
bookkeeping. It is vacuous whenever the store starts at or below the current end
of memory, which is why the `_of_le` forms carry no side condition at all.

## The opcode layer

Everything here is stated about the `MachineState` operations. A correspondence
proof holds an `EvmYul.EVM.step` on a full `EVM.State` instead, and must first
know that the step ran `MachineState.mstore`. `EvmYul.EVM.Proof.MemoryStep`
supplies that link and restates the results above one layer up — in particular
`le_size_memory_step_MSTORE` (in bounds after a real `MSTORE`) and
`H_return_step_MSTORE_RETURN_zero` (the canonical two-opcode residual).
-/

set_option autoImplicit false

namespace ffi.ByteArray

/-- `zeroes` is `Array.replicate` behind an `@[extern]`, so it has exactly the
requested size. Stated against `USize.toNat` rather than against any particular
`Nat`-cast spelling of the argument, because the padding lengths inside
`ByteArray.write` and `ByteArray.readWithPadding` normalise inconsistently. -/
@[simp] theorem size_zeroes (u : USize) : (ffi.ByteArray.zeroes u).size = u.toNat := by
  simp [ffi.ByteArray.zeroes, ByteArray.size]

/-- Padding by zero bytes is padding by nothing. -/
theorem zeroes_eq_empty {u : USize} (h : u.toNat = 0) :
    ffi.ByteArray.zeroes u = ByteArray.empty := by
  ext1; simp [ffi.ByteArray.zeroes, h]

/-- Recovering a `Nat` from the `USize` it was cast into, given no wraparound.
The padding length inside `ByteArray.write`'s dest-growing branch is a `Nat`
subtraction cast to `USize`, so every statement about how far a write grows
memory needs this. -/
theorem toNat_natCast_of_lt (n : ℕ) (h : n < 2 ^ System.Platform.numBits) :
    ({ toBitVec := (n : BitVec System.Platform.numBits) } : USize).toNat = n := by
  simp only [USize.toNat, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The padding count in `UInt256.toByteArray` is computed by `USize`
subtraction, so recovering it as a `Nat` needs the absence of wraparound. -/
theorem toNat_usizeSub_of_le (n : ℕ) (h : n ≤ 32) :
    ({ toBitVec := (32 : BitVec System.Platform.numBits)
        - (n : BitVec System.Platform.numBits) } : USize).toNat = 32 - n := by
  have hw : 32 < 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h' | h' <;> rw [h'] <;> omega
  have hn : n < 2 ^ System.Platform.numBits := by omega
  have h32 : (32 : BitVec System.Platform.numBits).toNat = 32 := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
  simp only [USize.toNat, BitVec.toNat_sub, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, h32]
  rw [show 2 ^ System.Platform.numBits - n + 32
        = 2 ^ System.Platform.numBits + (32 - n) from by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

end ffi.ByteArray

namespace ByteArray

@[simp] theorem self_append_empty (b : ByteArray) : b ++ ByteArray.empty = b := by ext1; simp

@[simp] theorem empty_append_self (b : ByteArray) : ByteArray.empty ++ b = b := by ext1; simp

/-- Appending zero padding is a no-op. The hypothesis is discharged by `simp` at
every call site below; it is phrased on `USize.toNat` so that it does not depend
on how the padding length was spelled. -/
theorem append_zeroes {b : ByteArray} {u : USize} (h : u.toNat = 0) :
    b ++ ffi.ByteArray.zeroes u = b := by
  rw [ffi.ByteArray.zeroes_eq_empty h, self_append_empty]

/-! ## Splicing

`write_eq_of_fits` produces a three-way `Array` append, and the read lemmas then
have to extract a span out of it. These are the three span positions. -/

/-- The middle summand of a three-way append is exactly what sits at its offset. -/
theorem _root_.Array.extract_append_middle (A B C : Array UInt8) (i j : ℕ)
    (hi : i = A.size) (hj : j = A.size + B.size) :
    (A ++ B ++ C).extract i j = B := by
  subst hi; subst hj; apply Array.ext'; simp

/-- A span ending inside the first summand only sees the first summand. -/
theorem _root_.Array.extract_append_of_le (A B C : Array UInt8) (i j : ℕ) (h : j ≤ A.size) :
    (A ++ B ++ C).extract i j = A.extract i j := by
  apply Array.ext'
  simp only [Array.toList_extract, Array.toList_append, List.extract_eq_take_drop,
    List.append_assoc, ← List.drop_take]
  rw [List.take_append_of_le_length (by simpa using h)]

/-- A span starting past the middle summand only sees the last summand. -/
theorem _root_.Array.extract_append_of_ge (A B C : Array UInt8) (i j : ℕ)
    (hij : i ≤ j) (h : A.size + B.size ≤ i) :
    (A ++ B ++ C).extract i j = C.extract (i - (A.size + B.size)) (j - (A.size + B.size)) := by
  apply Array.ext'
  simp only [Array.toList_extract, Array.toList_append, List.extract_eq_take_drop,
    List.append_assoc]
  rw [List.drop_append, List.drop_append,
      List.drop_eq_nil_of_le (by simp; omega), List.drop_eq_nil_of_le (by simp; omega),
      show j - (A.size + B.size) - (i - (A.size + B.size)) = j - i from by omega]
  simp [Nat.sub_sub]

/-- The last summand of a two-way append is exactly what sits at its offset.
The dest-growing branch of `write` produces `prefix ++ src` rather than the
three-way splice, because there is no tail left to keep. -/
theorem _root_.Array.extract_append_tail (A B : Array UInt8) (i j : ℕ)
    (hi : i = A.size) (hj : j = A.size + B.size) :
    (A ++ B).extract i j = B := by
  subst hi; subst hj; rw [Array.extract_append_right, Array.extract_size]

/-- Taking a prefix of `A ++ Z` where `Z` is exactly the shortfall of `A` against
`n`. This is the one shape the two `write` branches share: when `n ≤ A.size` the
padding `Z` is empty, and when `n > A.size` the prefix is all of `A ++ Z`. -/
theorem _root_.Array.extract_zero_append (A Z : Array UInt8) (n : ℕ)
    (hZ : Z.size = n - A.size) :
    (A ++ Z).extract 0 n = A.extract 0 n ++ Z := by
  rcases Nat.le_total n A.size with h | h
  · rw [Array.eq_empty_of_size_eq_zero (by omega : Z.size = 0)]
    simp
  · rw [Array.extract_eq_self_of_le (by simp; omega),
        Array.extract_eq_self_of_le h]

/-! ## Normal forms -/

/-- **`write` reduced.** Writing the whole of `src` at `destAddr`, with the span
inside `dest`, is the three-way splice. Every zero-padding term in the
definition of `write` has length `0` under these hypotheses. -/
theorem write_eq_of_fits (src dest : ByteArray) (destAddr len : ℕ)
    (hlen : 0 < len) (hsrc : src.size = len) (hfit : destAddr + len ≤ dest.size) :
    ByteArray.write src 0 dest destAddr len
      = ⟨dest.data.extract 0 destAddr ++ src.data
          ++ dest.data.extract (destAddr + len) dest.size⟩ := by
  unfold ByteArray.write
  rw [if_neg (by omega)]
  rw [if_neg (by simp [hsrc]; omega)]
  simp only [Nat.sub_zero, hsrc, Nat.min_self]
  rw [show min dest.size (destAddr + len) = destAddr + len from by omega,
      show destAddr + len - (destAddr + len) = 0 from by omega,
      show destAddr - dest.size = 0 from by omega]
  rw [append_zeroes (by simp), append_zeroes (by simp), Nat.add_zero]
  have hdata : src.data.extract 0 len = src.data := by
    rw [← hsrc]; exact Array.extract_size
  ext1
  simp [ByteArray.copySlice, hsrc, hdata]

/-- An in-bounds write does not resize the destination. -/
theorem size_write_of_fits (src dest : ByteArray) (destAddr len : ℕ)
    (hlen : 0 < len) (hsrc : src.size = len) (hfit : destAddr + len ≤ dest.size) :
    (ByteArray.write src 0 dest destAddr len).size = dest.size := by
  rw [write_eq_of_fits src dest destAddr len hlen hsrc hfit]
  show (_ : Array UInt8).size = _
  simp only [Array.size_append, Array.size_extract, ByteArray.size_data]
  have hs : src.data.size = len := by simpa using hsrc
  omega

/-- **`write` reduced, growing case.** When the written span reaches the end of
`dest` or past it, `write` takes its *other* branch: it zero-extends `dest` up to
`destAddr` and appends `src`, so there is no tail to keep and the result is
`dest[0, destAddr) ++ 0…0 ++ src`.

This is the branch a fresh frame takes. `MachineState.M` charges expansion into
`activeWords` and leaves `memory` alone, so a frame that has only ever charged
gas still has `memory.size = 0`; it is `write` itself, not the charge, that makes
memory big enough to read back from.

`hpad` rules out `USize` wraparound in the zero-padding length. It is vacuous
whenever `destAddr ≤ dest.size` and is the honest side condition otherwise: once
`destAddr - dest.size` reaches `2 ^ System.Platform.numBits` the padding really
does wrap and the write really does land somewhere else. -/
theorem write_eq_of_grows (src dest : ByteArray) (destAddr len : ℕ)
    (hlen : 0 < len) (hsrc : src.size = len) (hcov : dest.size ≤ destAddr + len)
    (hpad : destAddr - dest.size < 2 ^ System.Platform.numBits) :
    ByteArray.write src 0 dest destAddr len
      = ⟨dest.data.extract 0 destAddr ++ Array.replicate (destAddr - dest.size) 0
          ++ src.data⟩ := by
  have hsd : src.data.size = len := by simpa using hsrc
  have hZ : (ffi.ByteArray.zeroes (⟨(destAddr - dest.size : ℕ)⟩ : USize)).data
      = Array.replicate (destAddr - dest.size) 0 := by
    show Array.replicate
        (USize.toNat ⟨((destAddr - dest.size : ℕ) : BitVec System.Platform.numBits)⟩) 0 = _
    rw [ffi.ByteArray.toNat_natCast_of_lt _ hpad]
  unfold ByteArray.write
  rw [if_neg (by omega)]
  rw [if_neg (by simp [hsrc]; omega)]
  simp only [Nat.sub_zero, hsrc, Nat.min_self]
  rw [show min dest.size (destAddr + len) = dest.size from by omega,
      show dest.size - (destAddr + len) = 0 from by omega]
  rw [append_zeroes (by simp), Nat.add_zero]
  ext1
  simp only [ByteArray.copySlice, ByteArray.data_append, hZ, hsd, Nat.sub_zero,
    Nat.min_self, Nat.zero_add]
  have hzs : (Array.replicate (destAddr - dest.size) (0 : UInt8)).size
      = destAddr - dest.data.size := by
    simp [ByteArray.size_data]
  have htail : (dest.data ++ Array.replicate (destAddr - dest.size) 0).extract (destAddr + len)
      ((dest.data ++ Array.replicate (destAddr - dest.size) 0).size) = #[] := by
    apply Array.extract_eq_empty_of_le
    simp only [Nat.min_self, Array.size_append, Array.size_replicate, ByteArray.size_data]
    omega
  rw [Array.extract_zero_append _ _ _ hzs,
      Array.extract_eq_self_of_le (Nat.le_of_eq hsd), htail, Array.append_empty]

/-- **How far a `write` grows its destination.** Combined with
`size_write_of_fits`, this is the fact a caller needs in order to know that a
later read is in bounds: after writing `len` bytes at `destAddr`, memory is at
least `destAddr + len` long, whatever it was before. -/
theorem size_write (src dest : ByteArray) (destAddr len : ℕ)
    (hlen : 0 < len) (hsrc : src.size = len)
    (hpad : destAddr - dest.size < 2 ^ System.Platform.numBits) :
    (ByteArray.write src 0 dest destAddr len).size = max dest.size (destAddr + len) := by
  rcases Nat.lt_or_ge (destAddr + len) dest.size with h | h
  · rw [size_write_of_fits src dest destAddr len hlen hsrc (by omega)]
    omega
  · rw [write_eq_of_grows src dest destAddr len hlen hsrc h hpad]
    show (_ : Array UInt8).size = _
    have hsd : src.data.size = len := by simpa using hsrc
    simp only [Array.size_append, Array.size_extract, Array.size_replicate,
      ByteArray.size_data, hsd]
    omega

/-- **`readWithPadding` reduced.** An in-bounds read needs no padding and no
clamping, so it is a plain `extract`. -/
theorem readWithPadding_eq_extract (source : ByteArray) (addr len : ℕ)
    (hlen : 0 < len) (hlen64 : len < 2 ^ 64) (hfit : addr + len ≤ source.size) :
    source.readWithPadding addr len = source.extract addr (addr + len) := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  rw [if_neg (by omega)]
  simp only []
  rw [if_neg (by omega), show min len source.size = len from by omega]
  have hsize : (source.extract addr (addr + len)).size = len := by
    simp; omega
  rw [hsize, append_zeroes (by simp)]

/-! ## Read-over-write

The three cases of a read against a write: the read span is the written span, or
it lies entirely below it, or entirely above it. -/

/-- **Read-over-write.** Reading back exactly the span that was written returns
the source. -/
theorem readWithPadding_write_self (src dest : ByteArray) (destAddr len : ℕ)
    (hlen : 0 < len) (hlen64 : len < 2 ^ 64) (hsrc : src.size = len)
    (hfit : destAddr + len ≤ dest.size) :
    (ByteArray.write src 0 dest destAddr len).readWithPadding destAddr len = src := by
  rw [readWithPadding_eq_extract _ _ _ hlen hlen64
        (by rw [size_write_of_fits src dest destAddr len hlen hsrc hfit]; omega),
      write_eq_of_fits src dest destAddr len hlen hsrc hfit]
  have hA : (dest.data.extract 0 destAddr).size = destAddr := by
    simp only [Array.size_extract, ByteArray.size_data]
    omega
  have hB : src.data.size = len := by simpa using hsrc
  ext1
  simp only [ByteArray.data_extract]
  exact Array.extract_append_middle _ _ _ _ _ hA.symm (by omega)

/-- **Read-over-write, growing case.** Reading back a span that the write had to
grow memory to hold still returns the source. -/
theorem readWithPadding_write_self_of_grows (src dest : ByteArray) (destAddr len : ℕ)
    (hlen : 0 < len) (hlen64 : len < 2 ^ 64) (hsrc : src.size = len)
    (hcov : dest.size ≤ destAddr + len)
    (hpad : destAddr - dest.size < 2 ^ System.Platform.numBits) :
    (ByteArray.write src 0 dest destAddr len).readWithPadding destAddr len = src := by
  have hsz := size_write src dest destAddr len hlen hsrc hpad
  have hsd : src.data.size = len := by simpa using hsrc
  rw [readWithPadding_eq_extract _ _ _ hlen hlen64 (by omega),
      write_eq_of_grows src dest destAddr len hlen hsrc hcov hpad]
  have hP : (dest.data.extract 0 destAddr
      ++ Array.replicate (destAddr - dest.size) (0 : UInt8)).size = destAddr := by
    simp only [Array.size_append, Array.size_extract, Array.size_replicate,
      ByteArray.size_data, Nat.sub_zero]
    omega
  ext1
  simp only [ByteArray.data_extract]
  exact Array.extract_append_tail _ _ _ _ hP.symm (by omega)

/-- **Read-over-write, no bound on the destination.** The union of the in-bounds
and growing cases: reading back exactly the span that was written returns the
source whatever `dest.size` was, subject only to the `USize` non-wraparound
condition on the gap. This is the form callers should reach for — it needs no
prior knowledge of how big memory happened to be. -/
theorem readWithPadding_write_self_of_pad (src dest : ByteArray) (destAddr len : ℕ)
    (hlen : 0 < len) (hlen64 : len < 2 ^ 64) (hsrc : src.size = len)
    (hpad : destAddr - dest.size < 2 ^ System.Platform.numBits) :
    (ByteArray.write src 0 dest destAddr len).readWithPadding destAddr len = src := by
  rcases Nat.lt_or_ge (destAddr + len) dest.size with h | h
  · exact readWithPadding_write_self src dest destAddr len hlen hlen64 hsrc (by omega)
  · exact readWithPadding_write_self_of_grows src dest destAddr len hlen hlen64 hsrc h hpad

/-- **Frame, below.** A read entirely below the written span is unaffected. -/
theorem readWithPadding_write_of_le (src dest : ByteArray) (destAddr len a l : ℕ)
    (hlen : 0 < len) (hsrc : src.size = len) (hfit : destAddr + len ≤ dest.size)
    (hl : 0 < l) (hl64 : l < 2 ^ 64) (hbelow : a + l ≤ destAddr) :
    (ByteArray.write src 0 dest destAddr len).readWithPadding a l
      = dest.readWithPadding a l := by
  rw [readWithPadding_eq_extract _ _ _ hl hl64
        (by rw [size_write_of_fits src dest destAddr len hlen hsrc hfit]; omega),
      readWithPadding_eq_extract _ _ _ hl hl64 (by omega),
      write_eq_of_fits src dest destAddr len hlen hsrc hfit]
  have hA : (dest.data.extract 0 destAddr).size = destAddr := by
    simp only [Array.size_extract, ByteArray.size_data]
    omega
  ext1
  simp only [ByteArray.data_extract]
  rw [Array.extract_append_of_le _ _ _ _ _ (by omega)]
  apply Array.ext'
  simp only [Array.toList_extract, List.extract_eq_take_drop, List.drop_zero]
  rw [Nat.sub_zero, List.drop_take, List.take_take,
      show min (a + l - a) (destAddr - a) = a + l - a from by omega]

/-- **Frame, above.** A read entirely above the written span is unaffected. -/
theorem readWithPadding_write_of_ge (src dest : ByteArray) (destAddr len a l : ℕ)
    (hlen : 0 < len) (hsrc : src.size = len) (hfit : destAddr + len ≤ dest.size)
    (hl : 0 < l) (hl64 : l < 2 ^ 64) (habove : destAddr + len ≤ a)
    (hend : a + l ≤ dest.size) :
    (ByteArray.write src 0 dest destAddr len).readWithPadding a l
      = dest.readWithPadding a l := by
  rw [readWithPadding_eq_extract _ _ _ hl hl64
        (by rw [size_write_of_fits src dest destAddr len hlen hsrc hfit]; omega),
      readWithPadding_eq_extract _ _ _ hl hl64 hend,
      write_eq_of_fits src dest destAddr len hlen hsrc hfit]
  have hA : (dest.data.extract 0 destAddr).size = destAddr := by
    simp only [Array.size_extract, ByteArray.size_data]
    omega
  have hB : src.data.size = len := by simpa using hsrc
  ext1
  simp only [ByteArray.data_extract]
  rw [Array.extract_append_of_ge _ _ _ _ _ (by omega) (by omega), hA, hB]
  apply Array.ext'
  simp only [Array.toList_extract, List.extract_eq_take_drop]
  rw [show a + l - (destAddr + len) - (a - (destAddr + len)) = l from by omega,
      show a + l - a = l from by omega, List.drop_take, List.drop_drop,
      show destAddr + len + (a - (destAddr + len)) = a from by omega,
      List.take_take,
      show min l (dest.size - (destAddr + len) - (a - (destAddr + len))) = l from by omega]

end ByteArray

namespace EvmYul

/-- `UInt256.toByteArray` always produces exactly 32 bytes: the big-endian
expansion is at most 32 long (`length_toBytesBigEndian_le`) and the definition
left-pads to make up the difference. -/
theorem UInt256.size_toByteArray (v : UInt256) : (UInt256.toByteArray v).size = 32 := by
  have hle : (BE v.toNat).size ≤ 32 := by
    simpa [BE] using EvmYul.length_toBytesBigEndian_le (n := v.toNat) v.val.isLt
  unfold UInt256.toByteArray
  rw [ByteArray.size_append, ffi.ByteArray.size_zeroes,
      ffi.ByteArray.toNat_usizeSub_of_le _ hle]
  omega

namespace MachineState

/-! ## The `MachineState` layer

`mstore8` writes one byte and `mstore` writes a 32-byte big-endian word; both go
through `writeBytes`, hence through `ByteArray.write` at source offset `0`. -/

/-- Reading back the byte written by `MSTORE8`. -/
theorem readWithPadding_memory_mstore8 (μ : MachineState) (spos sval : UInt256)
    (hfit : spos.toNat + 1 ≤ μ.memory.size) :
    (μ.mstore8 spos sval).memory.readWithPadding spos.toNat 1
      = ⟨#[UInt8.ofNat sval.toNat]⟩ := by
  show (ByteArray.write ⟨#[UInt8.ofNat sval.toNat]⟩ 0 μ.memory spos.toNat 1).readWithPadding _ _ = _
  exact ByteArray.readWithPadding_write_self _ _ _ _ (by omega) (by norm_num) rfl hfit

/-- An in-bounds `MSTORE8` does not resize memory. -/
theorem size_memory_mstore8 (μ : MachineState) (spos sval : UInt256)
    (hfit : spos.toNat + 1 ≤ μ.memory.size) :
    (μ.mstore8 spos sval).memory.size = μ.memory.size := by
  show (ByteArray.write ⟨#[UInt8.ofNat sval.toNat]⟩ 0 μ.memory spos.toNat 1).size = _
  exact ByteArray.size_write_of_fits _ _ _ _ (by omega) rfl hfit

/-- **Reading back the word written by `MSTORE`.** -/
theorem readWithPadding_memory_mstore (μ : MachineState) (spos sval : UInt256)
    (hfit : spos.toNat + 32 ≤ μ.memory.size) :
    (μ.mstore spos sval).memory.readWithPadding spos.toNat 32 = sval.toByteArray := by
  show (ByteArray.write sval.toByteArray 0 μ.memory spos.toNat 32).readWithPadding _ _ = _
  exact ByteArray.readWithPadding_write_self _ _ _ _ (by omega) (by norm_num)
    (UInt256.size_toByteArray sval) hfit

/-- An in-bounds `MSTORE` does not resize memory. -/
theorem size_memory_mstore (μ : MachineState) (spos sval : UInt256)
    (hfit : spos.toNat + 32 ≤ μ.memory.size) :
    (μ.mstore spos sval).memory.size = μ.memory.size := by
  show (ByteArray.write sval.toByteArray 0 μ.memory spos.toNat 32).size = _
  exact ByteArray.size_write_of_fits _ _ _ _ (by omega) (UInt256.size_toByteArray sval) hfit

/-! ## Charged expansion is not an in-bounds hypothesis

`MachineState.M` is a `ℕ → ℕ → ℕ → ℕ` that every memory opcode feeds into
`activeWords`. It does not touch `memory`, so a frame that has charged expansion
for `[0, 32)` still has `memory.size = 0`. The lemmas below therefore do *not*
route through `M`; they get their in-bounds facts from the write itself. -/

/-- Updating `activeWords` — which is all that charging expansion via
`MachineState.M` ever does — leaves `memory` unchanged. Consequently `M` cannot
discharge a hypothesis about `memory.size`; see `size_memory_mstore_of_pad` for
what actually does. -/
theorem memory_activeWords_update (μ : MachineState) (n : UInt256) :
    ({ μ with activeWords := n } : MachineState).memory = μ.memory := rfl

/-- **How far an `MSTORE` grows memory.** After storing a word at `spos`, memory
is `max` of what it was and `spos + 32` — so `spos + 32 ≤ (μ.mstore spos sval).memory.size`
holds unconditionally (modulo `USize` wraparound), which is exactly the in-bounds
fact a following `RETURN` or `MLOAD` needs. -/
theorem size_memory_mstore_of_pad (μ : MachineState) (spos sval : UInt256)
    (hpad : spos.toNat - μ.memory.size < 2 ^ System.Platform.numBits) :
    (μ.mstore spos sval).memory.size = max μ.memory.size (spos.toNat + 32) := by
  show (ByteArray.write sval.toByteArray 0 μ.memory spos.toNat 32).size = _
  exact ByteArray.size_write _ _ _ _ (by omega) (UInt256.size_toByteArray sval) hpad

/-- **The in-bounds fact, established after the store rather than before it.**
This is the direct replacement for an appeal to charged expansion: `MSTORE` makes
its own span readable. -/
theorem le_size_memory_mstore (μ : MachineState) (spos sval : UInt256)
    (hpad : spos.toNat - μ.memory.size < 2 ^ System.Platform.numBits) :
    spos.toNat + 32 ≤ (μ.mstore spos sval).memory.size := by
  rw [size_memory_mstore_of_pad μ spos sval hpad]
  omega

/-- `MSTORE8` likewise grows memory to cover the byte it wrote. -/
theorem size_memory_mstore8_of_pad (μ : MachineState) (spos sval : UInt256)
    (hpad : spos.toNat - μ.memory.size < 2 ^ System.Platform.numBits) :
    (μ.mstore8 spos sval).memory.size = max μ.memory.size (spos.toNat + 1) := by
  show (ByteArray.write ⟨#[UInt8.ofNat sval.toNat]⟩ 0 μ.memory spos.toNat 1).size = _
  exact ByteArray.size_write _ _ _ _ (by omega) rfl hpad

/-- **Reading back an `MSTORE8`d byte, no side condition.** -/
theorem readWithPadding_memory_mstore8_of_le (μ : MachineState) (spos sval : UInt256)
    (hstart : spos.toNat ≤ μ.memory.size) :
    (μ.mstore8 spos sval).memory.readWithPadding spos.toNat 1
      = ⟨#[UInt8.ofNat sval.toNat]⟩ := by
  show (ByteArray.write ⟨#[UInt8.ofNat sval.toNat]⟩ 0 μ.memory spos.toNat 1).readWithPadding _ _ = _
  exact ByteArray.readWithPadding_write_self_of_pad _ _ _ _ (by omega) (by norm_num) rfl
    (by rw [show spos.toNat - μ.memory.size = 0 from by omega]; positivity)

/-- **Reading back an `MSTORE`d word without knowing how big memory was.** -/
theorem readWithPadding_memory_mstore_of_pad (μ : MachineState) (spos sval : UInt256)
    (hpad : spos.toNat - μ.memory.size < 2 ^ System.Platform.numBits) :
    (μ.mstore spos sval).memory.readWithPadding spos.toNat 32 = sval.toByteArray := by
  show (ByteArray.write sval.toByteArray 0 μ.memory spos.toNat 32).readWithPadding _ _ = _
  exact ByteArray.readWithPadding_write_self_of_pad _ _ _ _ (by omega) (by norm_num)
    (UInt256.size_toByteArray sval) hpad

/-- **Reading back an `MSTORE`d word, no side condition.** A store that starts at
or before the current end of memory has nothing to wrap, so the `USize` condition
is vacuous. Fresh frames (`memory.size = 0`, `spos = 0`) are the main instance. -/
theorem readWithPadding_memory_mstore_of_le (μ : MachineState) (spos sval : UInt256)
    (hstart : spos.toNat ≤ μ.memory.size) :
    (μ.mstore spos sval).memory.readWithPadding spos.toNat 32 = sval.toByteArray :=
  readWithPadding_memory_mstore_of_pad μ spos sval
    (by rw [show spos.toNat - μ.memory.size = 0 from by omega]; positivity)

/-! ## The `RETURN` bridge

`evmReturn` is the only thing standing between memory and the bytes a halting
`X` hands back: `H` reads `H_return` and returns it verbatim. -/

/-- `RETURN` publishes a padded read of memory, and touches nothing else that a
read depends on. -/
theorem H_return_evmReturn (μ : MachineState) (mstart s : UInt256) :
    (μ.evmReturn mstart s).H_return = μ.memory.readWithPadding mstart.toNat s.toNat := rfl

/-- **`MSTORE` then `RETURN`.** The bytes returned by a fragment that stores a
word and returns exactly that word are the word itself. This is the composite
shape a straight-line `MSTORE`/`RETURN` correspondence proof reduces to. -/
theorem H_return_evmReturn_mstore (μ : MachineState) (spos sval s : UInt256)
    (hs : s.toNat = 32) (hfit : spos.toNat + 32 ≤ μ.memory.size) :
    ((μ.mstore spos sval).evmReturn spos s).H_return = sval.toByteArray := by
  rw [H_return_evmReturn, hs]
  exact readWithPadding_memory_mstore μ spos sval hfit

/-- **`MSTORE` then `RETURN`, without a prior in-bounds hypothesis.** Same
composite as `H_return_evmReturn_mstore`, but asking only that the store start at
or before the current end of memory rather than that the whole span already fit.
This is the version a real caller can discharge: `H_return_evmReturn_mstore`'s
`hfit` cannot be obtained from charging expansion, because
`memory_activeWords_update` says the charge does not touch `memory`. -/
theorem H_return_evmReturn_mstore_of_le (μ : MachineState) (spos sval s : UInt256)
    (hs : s.toNat = 32) (hstart : spos.toNat ≤ μ.memory.size) :
    ((μ.mstore spos sval).evmReturn spos s).H_return = sval.toByteArray := by
  rw [H_return_evmReturn, hs]
  exact readWithPadding_memory_mstore_of_le μ spos sval hstart

/-- **The canonical fragment, hypothesis-free.** `MSTORE(0, v)` then
`RETURN(0, 32)` returns `v`, for *any* starting machine state — in particular for
a fresh frame, where `memory.size = 0`. This is the residual shape an
`EndpointAgrees`-style correspondence proof is left with once the `CfgState` side
has been discharged, and it needs nothing about memory going in. -/
theorem H_return_evmReturn_mstore_zero (μ : MachineState) (sval s : UInt256)
    (hs : s.toNat = 32) :
    ((μ.mstore ⟨0⟩ sval).evmReturn ⟨0⟩ s).H_return = sval.toByteArray :=
  H_return_evmReturn_mstore_of_le μ ⟨0⟩ sval s hs (by
    show (0 : ℕ) ≤ _
    exact Nat.zero_le _)

end MachineState

end EvmYul
