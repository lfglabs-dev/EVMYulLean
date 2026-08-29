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
* `ByteArray.readWithPadding_write_self` is read-over-write proper: reading back
  exactly the span that was just written returns the source. Its two companions
  `readWithPadding_write_of_le` and `readWithPadding_write_of_ge` are the frame
  half — a read disjoint from the written span does not see the write.
* The `MachineState` layer specialises these to the operations the semantics
  actually dispatches on: `readWithPadding_memory_mstore8`,
  `readWithPadding_memory_mstore`, and `H_return_evmReturn_mstore`, which is the
  composite a `MSTORE`-then-`RETURN` fragment needs — the bytes a contract
  returns are the word it stored.

Everything rests on `EvmYul.MachineStateOps` and the Lean core `ByteArray`
lemmas. No axiom is introduced and no proof is admitted.

## For consumers

`import EvmYul.EVM.Proof.Memory`. A proof that has to discharge a goal of the
shape `μ.memory.readWithPadding a l = …` wants, in rough order of usefulness:

| Goal shape | Lemma |
| --- | --- |
| bytes returned after `MSTORE`; `RETURN` | `EvmYul.MachineState.H_return_evmReturn_mstore` |
| `H_return` of an `evmReturn` | `EvmYul.MachineState.H_return_evmReturn` |
| read back an `MSTORE`d word | `EvmYul.MachineState.readWithPadding_memory_mstore` |
| read back an `MSTORE8`d byte | `EvmYul.MachineState.readWithPadding_memory_mstore8` |
| memory size across a store | `EvmYul.MachineState.size_memory_mstore{,8}` |
| read disjoint from a store | `ByteArray.readWithPadding_write_of_le` / `_of_ge` |
| generic read-over-write | `ByteArray.readWithPadding_write_self` |
| unfold `write` / `readWithPadding` | `ByteArray.write_eq_of_fits` / `readWithPadding_eq_extract` |

`EvmYul.UInt256.size_toByteArray` (a stored word is exactly 32 bytes) is the
side condition most of the `MSTORE` lemmas need supplied at their call sites.

Note on scope: the `_of_fits` side conditions are not incidental. `write` and
`readWithPadding` genuinely behave differently when a span runs past the end of
memory — `readWithoutPadding` clamps with `min len source.size`, which is the
*total* size rather than the remaining size — so the in-bounds hypotheses are
what make these equations true, not a convenience for the proof. A caller that
has already charged memory expansion (`MachineState.M`) is in bounds.
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

end MachineState

end EvmYul
