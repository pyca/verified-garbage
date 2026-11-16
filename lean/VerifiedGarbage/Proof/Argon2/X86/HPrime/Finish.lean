module

public import VerifiedGarbage.Proof.Argon2.X86.HPrime.Next
import VerifiedGarbage.Proof.Sha512.X86.Rounds
import VerifiedGarbage.Proof.MdStream.X86.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Blake2.X86.Stream.Common
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Blake2.X86.Blake2b
import VerifiedGarbage.Proof.Blake2.X86.LitB
import VerifiedGarbage.Proof.Blake2.X86.CompressB.Body
public import VerifiedGarbage.Proof.Argon2.X86.HPrime.CallsCT
public import VerifiedGarbage.Proof.Argon2.HPrime
import VerifiedGarbage.Proof.Argon2.Initial
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Blake2.X86.Stream.Finalize

/-! ### `Argon2.X86.HPrime.Output`, which only this module used -/

section

@[expose] public section

section

/-!
# Argon2 H′ on x86 (32-bit): the state of the body

`Body s₀ s`: between H′'s setup and its restore, `ebx` points to `scratch`,
`esp` is as on entry, memory has changed only in the output, `scratch` and
the stack below `esp`, and the caller's registers and the length prefix are
kept in `scratch`. `Out s₀ s k`: the output pointer and the bytes left, after
`k` output bytes. `copy_ok`: copying digest bytes to the output.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (copy outOff leftOff saved)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_addi wp_movm wp_store contains_addr)
open VG.WriteBytes

theorem bytesAt_writeBytes (m : Mem) (p : Addr) (xs : List Byte) (hn : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p xs.length = xs := by
  apply List.ext_getElem (by simp only [bytesAt, List.length_map, List.length_range])
  intro i _ hi
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes,
    Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : i < 2 ^ 64),
    hi, ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem bytesAt_take (m : Mem) (p : Addr) (n k : Nat) (hn : n ≤ k) :
    (bytesAt m p k).take n = bytesAt m p n := by
  simp only [bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left hn]

/-- The state of the body. -/
structure Body (s₀ s : State) : Prop where
  ebx : s.gpr .ebx = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [outR s₀, scrR s₀, stkR s₀] s₀.mem s.mem
  saved : ∀ p ∈ saved, s.mem.readW (addr (scr s₀) p.2) 32 = s₀.gpr p.1
  pfx : bytesAt s.mem (P s₀ + 832) 4 = Spec.Argon2.le32 (ol s₀)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem Body.ctx {s : State} (h : Body s₀ s) : Ctx (scr s₀) (esp₀ s₀) s :=
  ⟨h.ebx, h.esp, by have := hp.scr_fits; omega_arith, hp.esp_lo, by have := hp.esp_hi; omega_arith,
    (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp [h.wr, hp.wr], 0, by simp, by simp⟩),
    hp.stk_scr.sub_right (Region.sub_prefix (by decide))⟩

/-- A word of `scratch` from offset 832 on is kept by the hash macros. -/
theorem keeps_word {s t : State} (k : Keeps (scr s₀) (esp₀ s₀) s t) {d : Nat} (hd : 832 ≤ d)
    (hd' : d + 4 ≤ 16384) : t.mem.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 := by
  refine k.frame.readW (r := ⟨addr (scr s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  obtain e := scr_addr hp (d := d) (by omega_arith)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [e]; exact Offset.disjoint_base _ hd (by omega_arith)
  · rw [e]
    exact (hp.stk_scr.sub_right (Offset.sub_base _ (show d + 4 ≤ 16384 from hd'))).symm

theorem Body.keeps {s t : State} (h : Body s₀ s) (k : Keeps (scr s₀) (esp₀ s₀) s t) : Body s₀ t := by
  refine ⟨k.ebx.trans h.ebx, k.esp.trans h.esp, k.rd.trans h.rd, k.wr.trans h.wr,
    h.frame.trans (k.frame.sub fun r hr => ?_), fun q hq => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · have hb : 832 ≤ q.2 ∧ q.2 + 4 ≤ 16384 := by
      simp only [Impl.Argon2.X86.HPrime.saved, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> decide
    rw [keeps_word hp k hb.1 hb.2]; exact h.saved q hq
  · rw [← h.pfx]
    exact k.bytes (R := ⟨P s₀ + 832, 4⟩) (by simp) (Offset.disjoint_base _ (by decide) (by decide))
      (hp.stk_scr.sub_right (Offset.sub_base _ (by decide))).symm

end

/-! ## Copying digest bytes -/

/-- The output pointer after `k` output bytes. -/
def OutPtr (s₀ s : State) (k : Nat) : Prop :=
  s.mem.readW (addr (scr s₀) outOff) 32 = op s₀ + BitVec.ofNat 32 k

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem copy_ok {s : State} (h : Body s₀ s) {k n : Nat} (hk : OutPtr s₀ s k)
    (hn : s.gpr .esi = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) (hkn : k + n ≤ ol s₀) :
    WP isa copy s fun t => Body s₀ t ∧ OutPtr s₀ t (k + n) ∧
      bytesAt t.mem ((op s₀).setWidth 64 + BitVec.ofNat 64 k) n = bytesAt s.mem (P s₀ + 768) n ∧
      t.gpr .ebp = s.gpr .ebp ∧
      Frame [⟨(op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩, ⟨P s₀ + BitVec.ofNat 64 outOff, 4⟩]
        s.mem t.mem := by
  have hs := hp.scr_fits
  have ho := hp.out_fits
  unfold copy
  refine WP.seq (wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_movm
    (VG.Proof.Sha512.X86.ea_of (B := scr s₀) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ebx])
      outOff)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]
        exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩)
    fun s₃ u₃ => WP.block_nil ?_)
  obtain mem₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain edx₃ : s₃.gpr .edx = scr s₀ + 768 := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, h.ebx]
  obtain edi₃ : s₃.gpr .edi = op s₀ + BitVec.ofNat 32 k := by
    rw [u₃.gpr, u₂.mem, u₁.mem]; exact hk
  obtain esi₃ : s₃.gpr .esi = BitVec.ofNat 32 n := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hn]
  obtain rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  obtain wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]
  obtain e768 : (scr s₀ + 768).setWidth 64 = P s₀ + 768 := setWidth_add (d := 768) (by omega_arith)
  obtain b768 : (scr s₀ + 768).toNat = (scr s₀).toNat + 768 := by
    rw [BitVec.toNat_add, show (768 : BitVec 32).toNat = 768 from rfl]; omega_arith
  obtain bk : (op s₀ + BitVec.ofNat 32 k).toNat = (op s₀).toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_arith)]; omega_arith
  obtain eOut : addr (op s₀ + BitVec.ofNat 32 k) 0 = (op s₀).setWidth 64 + BitVec.ofNat 64 k := by
    rw [MdStream.X86.addr_add_ofNat (by omega_arith), Nat.add_zero]
  refine WP.seq (Proof.Blake2.X86.Stream.copyLoop_ok (w := 0) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (k := n) hn₁ (by omega_arith) (by rw [b768]; omega_arith)
    (by simp only [Proof.Blake2.bufOff, Nat.reduceDiv, Nat.mul_zero, Nat.add_zero]; rw [bk]; omega_arith)
    edx₃ edi₃ esi₃ (fun i hi => ?_) (fun i hi => ?_) ?_ fun t ht => ?_)
  · have : i < 64 := by omega_arith
    rw [rd₃, wr₃, e768, show P s₀ + 768 + BitVec.ofNat 64 i = P s₀ + BitVec.ofNat 64 (768 + i) by
      rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl]
    refine ⟨scrR s₀, by simp [hp.wr], ?_⟩
    exact Offset.contains_base _ (d := 768 + i) (n := 1) (k := 16384) (by omega_arith) (by omega_arith)
  · rw [wr₃]
    simp only [Proof.Blake2.bufOff, Nat.reduceDiv, Nat.mul_zero, eOut]
    refine ⟨outR s₀, by simp [hp.wr], ?_⟩
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact Offset.contains_base _ (d := k + i) (n := 1) (k := ol s₀) (by omega_arith) (by omega_arith)
  · rw [e768]
    simp only [Proof.Blake2.bufOff, Nat.reduceDiv, Nat.mul_zero, eOut]
    exact (hp.out_scr.sub_left (Offset.sub_base _ (d := k) (n := n) (k := ol s₀) (by omega_arith))).sub_right
      (Offset.sub_base (P s₀) (d := 768) (n := n) (k := 16384) (by omega_arith)) |>.symm
  -- The store of the output pointer.
  obtain o : ∀ x, x ≠ .edx → x ≠ .edi → x ≠ .esi → x ≠ .eax → t.gpr x = s.gpr x := fun x a b c d => by
    rw [ht.other x a b c d, u₃.other _ b, u₂.other _ a, u₁.other _ a]
  obtain ebxT : t.gpr .ebx = scr s₀ := by rw [o _ (by decide) (by decide) (by decide) (by decide), h.ebx]
  obtain wrT : t.wr = s₀.wr := ht.wr.trans wr₃
  have dstE : addr (op s₀ + BitVec.ofNat 32 k) (Proof.Blake2.bufOff 0) =
      (op s₀).setWidth 64 + BitVec.ofNat 64 k := eOut
  obtain lenL : (bytesAt s.mem (P s₀ + 768) n).length = n := by simp [bytesAt]
  obtain memT : t.mem = writeBytes s.mem ((op s₀).setWidth 64 + BitVec.ofNat 64 k)
      (bytesAt s.mem (P s₀ + 768) n) := by
    rw [ht.mem, dstE, e768, mem₃, List.take_of_length_le (by rw [lenL])]
  refine wp_store (VG.Proof.Sha512.X86.ea_of ebxT outOff)
    (by rw [wrT]; exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩)
    fun t' u => WP.block_nil ?_
  obtain eslot : addr (scr s₀) outOff = P s₀ + BitVec.ofNat 64 outOff := scr_addr hp (by decide)
  obtain F : Frame [⟨(op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩, ⟨P s₀ + BitVec.ofNat 64 outOff, 4⟩]
      s.mem t'.mem := by
    rw [u.mem, memT, eslot]
    refine ((writeBytes_frame s.mem _ _ (R := ⟨(op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩)
      (by rw [lenL]; exact Region.contains_self _ _)).mono (by simp)).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
  obtain outSub : Region.Sub ⟨(op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩ (outR s₀) :=
    Offset.sub_base _ (by omega_arith)
  obtain slotSub : Region.Sub ⟨P s₀ + BitVec.ofNat 64 outOff, 4⟩ (scrR s₀) :=
    Offset.sub_base _ (by decide)
  obtain keep : ∀ d, d + 4 ≤ 16384 → (d + 4 ≤ outOff ∨ outOff + 4 ≤ d) →
      t'.mem.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 := fun d hd hd' => by
    refine F.readW (r := ⟨addr (scr s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    rw [scr_addr hp (by omega_arith)]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((hp.out_scr.sub_left outSub).sub_right (Offset.sub_base _ hd)).symm
    · exact Offset.disjoint _ hd' (by omega_arith) (by simp only [outOff]; omega_arith)
  refine ⟨⟨by rw [u.gpr, ebxT], by rw [u.gpr, o _ (by decide) (by decide) (by decide) (by decide), h.esp],
      by rw [u.rd, ht.rd, rd₃], by rw [u.wr, wrT], ?_, fun q hq => ?_, ?_⟩, ?_, ?_,
    by rw [u.gpr, o _ (by decide) (by decide) (by decide) (by decide)], F⟩
  · exact h.frame.trans (F.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨outR s₀, by simp, outSub⟩
      · exact ⟨scrR s₀, by simp, slotSub⟩)
  · have hb : 832 ≤ q.2 ∧ q.2 + 4 ≤ outOff := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> decide
    rw [keep _ (by simp only [outOff] at hb; omega_arith) (.inl hb.2)]; exact h.saved q hq
  · rw [← h.pfx]
    refine Proof.Blake2.bytesAt_congr fun i hi => F.bytes (R := ⟨P s₀ + 832, 4⟩) (fun r hr => ?_)
      (by simp) hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((hp.out_scr.sub_left outSub).sub_right
        (Offset.sub_base (P s₀) (d := 832) (n := 4) (k := 16384) (by decide))).symm
    · exact Offset.disjoint (P s₀) (d := 832) (n := 4) (e := outOff) (k := 4) (by decide) (by decide)
        (by decide)
  · show _ = _
    rw [u.mem, Mem.readW_writeW_self32, ht.dstV, BitVec.add_assoc, BitVec.ofNat_add]
  · have wb : bytesAt t.mem ((op s₀).setWidth 64 + BitVec.ofNat 64 k) n = bytesAt s.mem (P s₀ + 768) n := by
      rw [memT]
      have := bytesAt_writeBytes s.mem ((op s₀).setWidth 64 + BitVec.ofNat 64 k)
        (bytesAt s.mem (P s₀ + 768) n) (by rw [lenL]; omega_arith)
      rwa [lenL] at this
    rw [← wb, u.mem]
    refine Proof.Blake2.bytesAt_congr fun i hi =>
      ((Frame.refl [⟨addr (scr s₀) outOff, 4⟩] t.mem).writeW (List.mem_singleton_self _) _
        (Region.contains_self _ _)).bytes (R := ⟨(op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩) ?_ (by simp; omega_arith) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    rw [eslot]
    exact (hp.out_scr.sub_left outSub).sub_right slotSub

end

end VG.Proof.Argon2.X86.HPrime

end

/-!
# Argon2 H′ on x86 (32-bit): the output

`Out s₀ s xs`: the output so far, `xs`, its pointer and the bytes left.
`emit_ok` writes a 32-byte prefix of the digest, `copyRemaining_ok` the last
bytes.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (copy outOff leftOff emitPrefix copyRemaining)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_movi wp_movm wp_store wp_subi contains_addr)

/-- The output so far. -/
structure Out (s₀ s : State) (xs : List Byte) : Prop where
  ptr : OutPtr s₀ s xs.length
  left : s.mem.readW (addr (scr s₀) leftOff) 32 = BitVec.ofNat 32 (ol s₀ - xs.length)
  bytes : bytesAt s.mem ((op s₀).setWidth 64) xs.length = xs
  len : xs.length ≤ ol s₀

/-- The digest. -/
abbrev digest (s₀ s : State) : List Byte := bytesAt s.mem (P s₀ + 768) 64

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- The output and its slots are kept by the hash macros. -/
theorem Out.keeps {s t : State} {xs : List Byte} (h : Out s₀ s xs)
    (k : Keeps (scr s₀) (esp₀ s₀) s t) : Out s₀ t xs := by
  refine ⟨?_, ?_, ?_, h.len⟩
  · show _ = _; rw [keeps_word hp k (by decide) (by decide)]; exact h.ptr
  · rw [keeps_word hp k (by decide) (by decide)]; exact h.left
  · have kb := k.bytes (R := ⟨(op s₀).setWidth 64, xs.length⟩)
      (by have := h.len; have := hp.out_fits; simp; omega_arith)
      ((hp.out_scr.sub_left (Region.sub_prefix h.len)).sub_right (Region.sub_prefix (by decide)))
      ((hp.stk_out.sub_right (Region.sub_prefix h.len)).symm)
    simp only at kb
    rw [kb]; exact h.bytes

/-- A word of `scratch` outside the output pointer's slot is kept by `copy`. -/
theorem copy_word {s t : State} {k n : Nat} (hkn : k + n ≤ ol s₀)
    (f : Frame [⟨(op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩, ⟨P s₀ + BitVec.ofNat 64 outOff, 4⟩]
      s.mem t.mem) {d : Nat} (hd : d + 4 ≤ 16384) (hd' : d + 4 ≤ outOff ∨ outOff + 4 ≤ d) :
    t.mem.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 := by
  have ho := hp.out_fits
  refine f.readW (r := ⟨addr (scr s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  rw [scr_addr hp (by omega_arith)]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ((hp.out_scr.sub_left (Offset.sub_base _ (by omega_arith))).sub_right
      (Offset.sub_base _ hd)).symm
  · exact Offset.disjoint _ hd' (by omega_arith) (by simp only [outOff]; omega_arith)

/-- Emit `n` digest bytes after the output `xs`. -/
theorem copyOut_ok {s : State} (b : Body s₀ s) {xs : List Byte} (h : Out s₀ s xs) {n : Nat}
    (hn : s.gpr .esi = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) (hkn : xs.length + n ≤ ol s₀) :
    WP isa copy s fun t => Body s₀ t ∧ t.gpr .ebp = s.gpr .ebp ∧
      bytesAt t.mem ((op s₀).setWidth 64) (xs.length + n) = xs ++ (digest s₀ s).take n ∧
      OutPtr s₀ t (xs.length + n) ∧
      t.mem.readW (addr (scr s₀) leftOff) 32 = s.mem.readW (addr (scr s₀) leftOff) 32 ∧
      digest s₀ t = digest s₀ s := by
  have ho := hp.out_fits
  refine (copy_ok hp b h.ptr hn hn₁ hn₂ hkn).mono ?_
  rintro t ⟨bt, pt, bytes, ebp, f⟩
  refine ⟨bt, ebp, ?_, pt, copy_word hp hkn f (by decide) (by decide), ?_⟩
  swap
  · refine Proof.Blake2.bytesAt_congr fun i hi => f.bytes (R := ⟨P s₀ + 768, 64⟩) (fun r hr => ?_)
      (by simp) hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((hp.out_scr.sub_left (Offset.sub_base _ (d := xs.length) (n := n) (k := ol s₀) (by omega_arith))).sub_right
        (Offset.sub_base (P s₀) (d := 768) (n := 64) (k := 16384) (by decide))).symm
    · exact Offset.disjoint (P s₀) (d := 768) (n := 64) (e := outOff) (k := 4) (by decide) (by decide)
        (by decide)
  obtain old : bytesAt t.mem ((op s₀).setWidth 64) xs.length = bytesAt s.mem ((op s₀).setWidth 64) xs.length := by
    refine Proof.Blake2.bytesAt_congr fun i hi => f.bytes (R := ⟨(op s₀).setWidth 64, xs.length⟩)
      (fun r hr => ?_) (by have := h.len; simp; omega_arith) hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)
    · exact (hp.out_scr.sub_left (Region.sub_prefix (by omega_arith))).sub_right
        (Offset.sub_base _ (by decide))
  rw [Proof.Blake2.bytesAt_add, bytes, bytesAt_take _ _ _ _ hn₂, old, h.bytes]

/-- Emit a 32-byte prefix of the digest. -/
theorem emit_ok {s : State} (b : Body s₀ s) {xs : List Byte} (h : Out s₀ s xs)
    (hkn : xs.length + 32 ≤ ol s₀) :
    WP isa emitPrefix s fun t => Body s₀ t ∧ t.gpr .ebp = s.gpr .ebp ∧
      Out s₀ t (xs ++ (digest s₀ s).take 32) ∧ digest s₀ t = digest s₀ s := by
  have ho := hp.out_fits
  have hs := hp.scr_fits
  unfold emitPrefix
  refine WP.seq (wp_movi fun s₁ u₁ => WP.block_nil ?_)
  obtain b₁ : Body s₀ s₁ := ⟨by rw [u₁.other _ (by decide), b.ebx], by rw [u₁.other _ (by decide), b.esp],
    by rw [u₁.rd, b.rd], by rw [u₁.wr, b.wr], by rw [u₁.mem]; exact b.frame,
    fun q hq => by rw [u₁.mem]; exact b.saved q hq, by rw [u₁.mem]; exact b.pfx⟩
  obtain h₁ : Out s₀ s₁ xs := ⟨by show _ = _; rw [u₁.mem]; exact h.ptr, by rw [u₁.mem]; exact h.left,
    by rw [u₁.mem]; exact h.bytes, h.len⟩
  refine WP.seq ((copyOut_ok hp b₁ h₁ u₁.gpr (by decide) (by decide) hkn).mono
    fun s₂ ⟨b₂, e₂, by₂, p₂, l₂, d₂⟩ => ?_)
  obtain rl : InRegions (s₂.rd ++ s₂.wr) (addr (scr s₀) leftOff) 4 := by
    rw [b₂.rd, b₂.wr]; exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩
  refine wp_movm (VG.Proof.Sha512.X86.ea_of b₂.ebx leftOff) rl fun s₃ u₃ => wp_subi fun s₄ u₄ _ => ?_
  obtain ebx₄ : s₄.gpr .ebx = scr s₀ := by rw [u₄.other _ (by decide), u₃.other _ (by decide), b₂.ebx]
  obtain wl : InRegions s₄.wr (addr (scr s₀) leftOff) 4 := by
    rw [u₄.wr, u₃.wr, b₂.wr]; exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩
  refine wp_store (VG.Proof.Sha512.X86.ea_of ebx₄ leftOff) wl fun s₅ u₅ => WP.block_nil ?_
  obtain m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  obtain d₁ : digest s₀ s₁ = digest s₀ s := by simp only [digest, u₁.mem]
  obtain v₄ : s₄.gpr .eax = BitVec.ofNat 32 (ol s₀ - (xs.length + 32)) := by
    rw [u₄.gpr, u₃.gpr, l₂, u₁.mem, h.left]
    exact (Proof.Sha256.X86.Stream.sub_ofNat (a := ol s₀ - xs.length) (b := 32) (by omega_arith)).trans
      (by congr 1)
  obtain e₅ : s₅.mem = s₂.mem.writeW (P s₀ + BitVec.ofNat 64 leftOff) (BitVec.ofNat 32 (ol s₀ - (xs.length + 32))) := by
    rw [u₅.mem, m₄, v₄, scr_addr hp (by decide)]
  obtain F : Frame [⟨P s₀ + BitVec.ofNat 64 leftOff, 4⟩] s₂.mem s₅.mem := by
    rw [e₅]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain keepW : ∀ d, d + 4 ≤ 16384 → (d + 4 ≤ leftOff ∨ leftOff + 4 ≤ d) →
      s₅.mem.readW (addr (scr s₀) d) 32 = s₂.mem.readW (addr (scr s₀) d) 32 := fun d hd hd' => by
    rw [e₅, scr_addr hp (by omega_arith)]
    exact Mem.readW_writeW_sep (Offset.sep _ hd' (by omega_arith) (by simp only [leftOff]; omega_arith)) (by decide)
  obtain keepB : ∀ R : Region, R.len ≤ 2 ^ 64 → R.Disjoint ⟨P s₀ + BitVec.ofNat 64 leftOff, 4⟩ →
      bytesAt s₅.mem R.base R.len = bytesAt s₂.mem R.base R.len := fun R hR hd =>
    Proof.Blake2.bytesAt_congr fun i hi => F.bytes (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd) hR hi
  obtain slotScr : Region.Sub ⟨P s₀ + BitVec.ofNat 64 leftOff, 4⟩ (scrR s₀) := Offset.sub_base _ (by decide)
  obtain len' : (xs ++ (digest s₀ s).take 32).length = xs.length + 32 := by
    simp [digest, bytesAt]
  refine ⟨⟨by rw [u₅.gpr, ebx₄], by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), b₂.esp],
      by rw [u₅.rd, u₄.rd, u₃.rd, b₂.rd], by rw [u₅.wr, u₄.wr, u₃.wr, b₂.wr],
      b₂.frame.trans (F.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, slotScr⟩),
      fun q hq => ?_, ?_⟩,
    by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), e₂, u₁.other _ (by decide)], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have hb : 832 ≤ q.2 ∧ q.2 + 4 ≤ leftOff := by
      simp only [Impl.Argon2.X86.HPrime.saved, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> decide
    rw [keepW _ (by simp only [leftOff] at hb; omega_arith) (.inl hb.2)]; exact b₂.saved q hq
  · rw [keepB ⟨P s₀ + 832, 4⟩ (by simp) (Offset.disjoint (P s₀) (d := 832) (n := 4) (e := leftOff) (k := 4)
      (by decide) (by decide) (by decide))]
    exact b₂.pfx
  · show _ = _
    rw [len', keepW _ (by decide) (by decide)]; exact p₂
  · rw [len', e₅, scr_addr hp (by decide), Mem.readW_writeW_self32]
  · rw [len']
    obtain k₁ := keepB ⟨(op s₀).setWidth 64, xs.length + 32⟩ (by simp; omega_arith)
      ((hp.out_scr.sub_left (Region.sub_prefix (by omega_arith))).sub_right slotScr)
    simp only at k₁
    rw [k₁, by₂, d₁]
  · rw [len']; exact hkn
  · have k₂ := keepB ⟨P s₀ + 768, 64⟩ (by simp) (Offset.disjoint (P s₀) (d := 768) (n := 64)
      (e := leftOff) (k := 4) (by decide) (by decide) (by decide))
    simp only at k₂
    show bytesAt _ _ _ = bytesAt _ _ _
    rw [k₂]; exact d₂.trans d₁

/-- Copy the bytes left. -/
theorem copyRemaining_ok {s : State} (b : Body s₀ s) {xs : List Byte} (h : Out s₀ s xs)
    (hn₁ : xs.length < ol s₀) (hn₂ : ol s₀ - xs.length ≤ 64) :
    WP isa copyRemaining s fun t => Body s₀ t ∧ t.gpr .ebp = s.gpr .ebp ∧
      bytesAt t.mem ((op s₀).setWidth 64) (ol s₀) = xs ++ (digest s₀ s).take (ol s₀ - xs.length) := by
  have hs := hp.scr_fits
  unfold copyRemaining
  obtain rl : InRegions (s.rd ++ s.wr) (addr (scr s₀) leftOff) 4 := by
    rw [b.rd, b.wr]; exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩
  refine WP.seq (wp_movm (VG.Proof.Sha512.X86.ea_of b.ebx leftOff) rl fun s₁ u₁ => WP.block_nil ?_)
  obtain b₁ : Body s₀ s₁ := ⟨by rw [u₁.other _ (by decide), b.ebx], by rw [u₁.other _ (by decide), b.esp],
    by rw [u₁.rd, b.rd], by rw [u₁.wr, b.wr], by rw [u₁.mem]; exact b.frame,
    fun q hq => by rw [u₁.mem]; exact b.saved q hq, by rw [u₁.mem]; exact b.pfx⟩
  obtain h₁ : Out s₀ s₁ xs := ⟨by show _ = _; rw [u₁.mem]; exact h.ptr, by rw [u₁.mem]; exact h.left,
    by rw [u₁.mem]; exact h.bytes, h.len⟩
  refine (copyOut_ok hp b₁ h₁ (n := ol s₀ - xs.length) (by rw [u₁.gpr, h.left]) (by omega_arith) hn₂
    (by omega_arith)).mono fun t ⟨bt, et, byt, _, _, _⟩ => ⟨bt, by rw [et, u₁.other _ (by decide)], ?_⟩
  rw [show xs.length + (ol s₀ - xs.length) = ol s₀ by omega_arith] at byt
  rw [byt]; simp only [digest, u₁.mem]

end

end VG.Proof.Argon2.X86.HPrime

end

end


@[expose] public section

section

section

/-!
# Argon2 H′ on x86 (32-bit): the first digest

`first_ok`: `first` leaves H(min(out_len, 64), LE32(out_len) ‖ input) at the
start of the digest, `scratch[768, 832)`. The input is read before anything
is written to the output, so the two may overlap.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (init update finalize absorbFixed chooseLength absorbInput finishInput
  first leftOff)
open VG.Proof.Sha256.X86.Stream (Upd Fupd wp_movi wp_movm wp_cmpi)
open VG.Proof.Blake2.X86.CompressB (wp_addC wp_adcC)
open VG.Impl.Sha512.X86 (at_)

/-- Steps that keep memory, the permissions, `ebx`, `ebp` and `esp`. -/
theorem Keeps.same {B E : BitVec 32} {s t : State} (hb : t.gpr .ebx = s.gpr .ebx)
    (hp : t.gpr .ebp = s.gpr .ebp) (hs : t.gpr .esp = s.gpr .esp) (hm : t.mem = s.mem)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : Keeps B E s t :=
  ⟨hb, hp, hs, hrd, hwr, hm ▸ Frame.refl _ _⟩

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem arg_addr {i : Nat} (hi : i < 5) :
    addr (esp₀ s₀) (4 + 4 * i) = (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
  addr_eq (by have := hp.esp_hi; omega_arith)

theorem arg_sub {i : Nat} (hi : i < 5) : Region.Sub ⟨addr (esp₀ s₀) (4 + 4 * i), 4⟩ (argR s₀) := by
  show Region.Sub _ ⟨addr (esp₀ s₀) (4 + 4 * 0), 20⟩
  rw [arg_addr hp hi, arg_addr hp (by decide)]
  exact Offset.sub _ (by omega_arith) (by omega_arith)

/-- The arguments are kept in the body. -/
theorem Body.arg {s : State} (b : Body s₀ s) {i : Nat} (hi : i < 5) :
    s.mem.readW (addr (esp₀ s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  have he := hp.esp_hi
  have hl := hp.esp_lo
  refine b.frame.readW (r := ⟨addr (esp₀ s₀) (4 + 4 * i), 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.arg_out.sub_left (arg_sub hp hi)
  · exact hp.arg_scr.sub_left (arg_sub hp hi)
  · show Region.Disjoint _ ⟨(esp₀ s₀ - BitVec.ofNat 32 60).setWidth 64, 60⟩
    rw [arg_addr hp hi, Taint.sub_setWidth hl]
    exact Offset.disjoint_below _ (by omega_arith)

theorem Body.arg_in {s : State} (b : Body s₀ s) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) (4 + 4 * i)) 4 := by
  refine ⟨argR s₀, by simp [b.rd, hp.rd], ?_⟩
  show Region.Contains ⟨addr (esp₀ s₀) (4 + 4 * 0), 20⟩ _ _
  rw [arg_addr hp hi, arg_addr hp (by decide)]
  exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)

omit hp in
theorem Out.same {s t : State} {xs : List Byte} (h : Out s₀ s xs) (hm : t.mem = s.mem) : Out s₀ t xs :=
  ⟨by show _ = _; rw [hm]; exact h.ptr, by rw [hm]; exact h.left, by rw [hm]; exact h.bytes, h.len⟩

/-- `edx := min(out_len, 64)`. -/
theorem choose_ok {s : State} (b : Body s₀ s) (o : Out s₀ s []) :
    WP isa chooseLength s fun t => t.gpr .edx = BitVec.ofNat 32 (min (ol s₀) 64) ∧
      Keeps (scr s₀) (esp₀ s₀) s t := by
  have hs := hp.scr_fits
  obtain hol := (arg s₀ 3).isLt
  unfold chooseLength
  obtain rl : InRegions (s.rd ++ s.wr) (addr (scr s₀) leftOff) 4 := by
    rw [b.rd, b.wr]
    exact ⟨scrR s₀, by simp [hp.wr], Proof.Sha256.X86.Stream.contains_addr (by decide) (by decide) hs⟩
  refine WP.seq (wp_movm (VG.Proof.Sha512.X86.ea_of b.ebx leftOff) rl fun s₁ u₁ =>
    wp_cmpi fun s₂ f₂ cf₂ _ => WP.block_nil ?_)
  obtain e₁ : s₁.gpr .edx = BitVec.ofNat 32 (ol s₀) := by rw [u₁.gpr, o.left]; rfl
  have k₂ : Keeps (scr s₀) (esp₀ s₀) s s₂ := Keeps.same
    (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.gpr, u₁.other _ (by decide)])
    (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.mem, u₁.mem]) (by rw [f₂.rd, u₁.rd])
    (by rw [f₂.wr, u₁.wr])
  refine WP.ite (decide (ol s₀ < 65)) (by
      show s₂.cf = _
      rw [cf₂, e₁, Proof.Sha256.X86.Stream.toNat_ofNat_lt hol]; rfl)
    (fun h => WP.block_nil ⟨?_, k₂⟩) (fun h => wp_movi fun s₃ u₃ => WP.block_nil ⟨?_, ?_⟩)
  · have : ol s₀ ≤ 64 := by simp only [decide_eq_true_eq] at h; omega_arith
    rw [f₂.gpr, e₁, Nat.min_eq_left this]
  · have : 64 ≤ ol s₀ := by simp only [decide_eq_false_iff_not] at h; omega_arith
    rw [u₃.gpr, Nat.min_eq_right this]; rfl
  · exact k₂.trans (Keeps.same (u₃.other _ (by decide)) (u₃.other _ (by decide)) (u₃.other _ (by decide))
      u₃.mem u₃.rd u₃.wr)

end

/-! ## The steps of `first` -/

/-- The state before and between the steps of `first`: the body, no output
yet, `ebp` and the input kept. -/
structure F0 (s₀ s : State) : Prop where
  body : Body s₀ s
  out : Out s₀ s []
  ebp : s.gpr .ebp = s₀.gpr .ebp
  input : bytesAt s.mem ((inp s₀).setWidth 64) (inl s₀) = bytesAt s₀.mem ((inp s₀).setWidth 64) (inl s₀)

/-- The length of the first digest. -/
abbrev nF (s₀ : State) : Nat := min (ol s₀) 64

/-- The input, on entry. -/
abbrev inB (s₀ : State) : List Byte := bytesAt s₀.mem ((inp s₀).setWidth 64) (inl s₀)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem F0.keeps {s t : State} (h : F0 s₀ s) (k : Keeps (scr s₀) (esp₀ s₀) s t) : F0 s₀ t := by
  refine ⟨h.body.keeps hp k, h.out.keeps hp k, k.ebp.trans h.ebp, ?_⟩
  have hif := hp.in_fits
  have := k.bytes (R := inR s₀) (by simp; omega_arith)
    (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in.symm
  simp only at this
  rw [this, h.input]

theorem nF_pos : 1 ≤ nF s₀ := by have := hp.ol_pos; simp only [nF]; omega_arith

theorem first_choose {s : State} (h : F0 s₀ s) :
    WP isa chooseLength s fun t => F0 s₀ t ∧ t.gpr .edx = BitVec.ofNat 32 (nF s₀) :=
  (choose_ok hp h.body h.out).mono fun _ ⟨e, k⟩ => ⟨h.keeps hp k, e⟩

theorem first_init {s : State} (h : F0 s₀ s ∧ s.gpr .edx = BitVec.ofNat 32 (nF s₀)) :
    WP isa init s fun t => F0 s₀ t ∧
      Repr b (Spec.Blake2.init b (nF s₀) 0) t.mem (P s₀) [] := by
  obtain c := h.1.body.ctx hp
  refine (init_ok c h.2 (nF_pos hp) (Nat.min_le_right _ _)).mono fun t ⟨r, cs, rd, wr, f⟩ => ⟨?_, r⟩
  refine h.1.keeps hp (Keeps.of_call (of_callee cs) rd wr f fun r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, below_sub (by decide) c.lo⟩

theorem pfx_cov {s : State} (b : Body s₀ s) : Covers [⟨P s₀ + BitVec.ofNat 64 832, 4⟩] s.wr := by
  rw [b.wr, hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, 832, rfl, by simp⟩

theorem first_fixed {s : State}
    (h : F0 s₀ s ∧ Repr b (Spec.Blake2.init b (nF s₀) 0) s.mem (P s₀) []) :
    WP isa (absorbFixed 832 4) s fun t => F0 s₀ t ∧
      Repr b (Spec.Blake2.init b (nF s₀) 0) t.mem (P s₀) (Spec.Argon2.le32 (ol s₀)) := by
  have hs := hp.scr_fits
  refine (absorbFixed_ok (h.1.body.ctx hp) (offset := 832) (size := 4) (by omega_arith) (by decide)
    (by decide) (pfx_cov hp h.1.body) (hp.stk_scr.sub_right (Offset.sub_base _ (by decide))) h.2).mono
    fun t ⟨r, k⟩ => ⟨h.1.keeps hp k, ?_⟩
  rw [show BitVec.ofNat 64 832 = (832 : Addr) from rfl, h.1.body.pfx] at r
  exact r

/-- The instructions before `absorbInput`'s call of `update`. -/
theorem absorbInput_blk {s : State} (h : F0 s₀ s) :
    WP isa (.block [.mov .ecx (.imm 4), .mov .edx (.imm 0), .mov .esi (.mem (at_ .esp 4)),
      .mov .edi (.mem (at_ .esp 8))]) s fun t =>
      UpdateIn (scr s₀) (esp₀ s₀) (inp s₀) (inl s₀) 4 0 t ∧ Keeps (scr s₀) (esp₀ s₀) s t ∧ t.mem = s.mem := by
  have b := h.body
  refine wp_movi fun s₄ u₄ => wp_movi fun s₅ u₅ =>
    wp_movm (VG.Proof.Sha512.X86.ea_of (by rw [u₅.other _ (by decide), u₄.other _ (by decide), b.esp])
      4) (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact b.arg_in hp (i := 0) (by decide)) fun s₆ u₆ =>
    wp_movm (VG.Proof.Sha512.X86.ea_of (by
        rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), b.esp]) 8)
      (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact b.arg_in hp (i := 1) (by decide)) fun s₇ u₇ =>
    WP.block_nil ?_
  obtain m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  obtain o₇ : ∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → s₇.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₇.other _ h4, u₆.other _ h3, u₅.other _ h2, u₄.other _ h1]
  obtain k₇ : Keeps (scr s₀) (esp₀ s₀) s s₇ := Keeps.same (o₇ _ (by decide) (by decide) (by decide) (by decide))
    (o₇ _ (by decide) (by decide) (by decide) (by decide)) (o₇ _ (by decide) (by decide) (by decide) (by decide))
    m₇ (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd]) (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr])
  obtain b₇ := b.keeps hp k₇
  refine ⟨⟨b₇.ctx hp, ?_, ?_, ?_, ?_, ?_⟩, k₇, m₇⟩
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem]; exact b.arg hp (i := 0) (by decide)
  · rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem, b.arg hp (i := 1) (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  · rw [b₇.rd, b₇.wr, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨inR s₀, by simp, 0, by simp, by simp⟩

theorem first_input {s : State}
    (h : F0 s₀ s ∧ Repr b (Spec.Blake2.init b (nF s₀) 0) s.mem (P s₀) (Spec.Argon2.le32 (ol s₀))) :
    WP isa absorbInput s fun t => F0 s₀ t ∧
      Repr b (Spec.Blake2.init b (nF s₀) 0) t.mem (P s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀) := by
  have hif := hp.in_fits
  obtain hil := (arg s₀ 1).isLt
  unfold absorbInput
  refine WP.seq ((absorbInput_blk hp h.1).mono fun s₇ ⟨⟨c₇, esi₇, edi₇, x₇, y₇, hDc⟩, k₇, m₇⟩ => ?_)
  obtain cnt₇ : s₇.gpr .edx ++ s₇.gpr .ecx = BitVec.ofNat 64 (Spec.Argon2.le32 (ol s₀)).length := by
    rw [Proof.Argon2.le32_length, x₇, y₇]; rfl
  obtain F₇ := h.1.keeps hp k₇
  refine (update_ok c₇ (h0 := Spec.Blake2.init Spec.Blake2.b (nF s₀) 0) esi₇ edi₇ hif hDc
    (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in (by rw [m₇]; exact h.2) cnt₇
    (by rw [Proof.Argon2.le32_length]; omega_arith)).mono fun s₈ ⟨r₈, cs₈, rd₈, wr₈, f₈⟩ => ?_
  rw [F₇.input] at r₈
  refine ⟨F₇.keeps hp (Keeps.of_call (of_callee cs₈) rd₈ wr₈ f₈ fun r hr => ?_), r₈⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

/-- The count of the prefix and the input, as `finishInput` passes it. -/
abbrev cntLo (s₀ : State) : BitVec 32 := BitVec.ofNat 32 (inl s₀ + 4)
abbrev cntHi (s₀ : State) : BitVec 32 := BitVec.ofNat 32 ((inl s₀ + 4) / 2 ^ 32)

/-- The instructions before `finishInput`'s call of `finalize`. -/
theorem finishInput_blk {s : State} (h : F0 s₀ s) :
    WP isa (.block [.mov .ecx (.mem (at_ .esp 8)), .mov .edx (.imm 0), .alu .add .ecx (.imm 4),
      .alu .adc .edx (.imm 0)]) s fun t =>
      FinalizeIn (scr s₀) (esp₀ s₀) (cntLo s₀) (cntHi s₀) t ∧ Keeps (scr s₀) (esp₀ s₀) s t ∧
        t.mem = s.mem := by
  obtain hil := (arg s₀ 1).isLt
  have b := h.body
  refine wp_movm (VG.Proof.Sha512.X86.ea_of b.esp 8) (b.arg_in hp (i := 1) (by decide))
    fun s₉ u₉ => wp_movi fun s₁₀ u₁₀ => wp_addC fun s₁₁ u₁₁ cf₁₁ => wp_adcC cf₁₁ fun s₁₂ u₁₂ _ =>
    WP.block_nil ?_
  obtain m₁₂ : s₁₂.mem = s.mem := by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]
  obtain o₁₂ : ∀ r, r ≠ .ecx → r ≠ .edx → s₁₂.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₁₂.other _ h2, u₁₁.other _ h1, u₁₀.other _ h2, u₉.other _ h1]
  obtain k₁₂ : Keeps (scr s₀) (esp₀ s₀) s s₁₂ := Keeps.same (o₁₂ _ (by decide) (by decide))
    (o₁₂ _ (by decide) (by decide)) (o₁₂ _ (by decide) (by decide)) m₁₂
    (by rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd]) (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr])
  obtain ecx₉ : s₉.gpr .ecx = BitVec.ofNat 32 (inl s₀) := by
    rw [u₉.gpr, b.arg hp (i := 1) (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨⟨(b.keeps hp k₁₂).ctx hp, ?_, ?_⟩, k₁₂, m₁₂⟩
  · show _ = BitVec.ofNat 32 (inl s₀ + 4)
    rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), ecx₉, BitVec.ofNat_add]; rfl
  · show _ = BitVec.ofNat 32 ((inl s₀ + 4) / 2 ^ 32)
    rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.gpr, u₁₀.other _ (by decide), ecx₉]
    rw [← Proof.Blake2.X86.Stream.carry_ofNat (inl s₀) 4 (by decide), Nat.div_eq_of_lt hil]
    rfl

theorem first_finish {s : State}
    (h : F0 s₀ s ∧ Repr b (Spec.Blake2.init b (nF s₀) 0) s.mem (P s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀)) :
    WP isa finishInput s fun t => F0 s₀ t ∧
      (digest s₀ t).take (nF s₀) = Spec.Argon2.H (nF s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀) := by
  have hif := hp.in_fits
  unfold finishInput
  refine WP.seq ((finishInput_blk hp h.1).mono fun s₁₂ ⟨⟨c₁₂, x₁₂, y₁₂⟩, k₁₂, m₁₂⟩ => ?_)
  obtain cnt : s₁₂.gpr .edx ++ s₁₂.gpr .ecx =
      BitVec.ofNat 64 (Spec.Argon2.le32 (ol s₀) ++ inB s₀).length := by
    rw [x₁₂, y₁₂, List.length_append, Proof.Argon2.le32_length]
    simp only [inB, bytesAt, List.length_map, List.length_range]
    apply BitVec.eq_of_toNat_eq
    rw [Proof.Blake2.X86.Stream.append_ofNat (by omega_arith), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  obtain F₁₂ := h.1.keeps hp k₁₂
  refine (finalize_ok c₁₂ (by rw [m₁₂]; exact h.2) cnt
    (by simp only [List.length_append, Proof.Argon2.le32_length, inB, bytesAt, List.length_map,
      List.length_range]; omega_arith)).mono ?_
  rintro t ⟨d, cs, rd, wr, f⟩
  refine ⟨F₁₂.keeps hp (Keeps.of_call (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> exact cs _ (by decide) (by decide)) rd wr f fun r hr => ?_), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · show (bytesAt t.mem ((scr s₀).setWidth 64 + 768) 64).take _ = _
    rw [d, Proof.Argon2.H_stream]

/-- `first` hashes the length prefix and the input. -/
theorem first_ok {s : State} (h : F0 s₀ s) :
    WP isa first s fun t => F0 s₀ t ∧
      (digest s₀ t).take (nF s₀) = Spec.Argon2.H (nF s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀) := by
  unfold first
  exact WP.seq ((first_choose hp h).mono fun _ h₁ => WP.seq ((first_init hp h₁).mono fun _ h₂ =>
    WP.seq ((first_fixed hp h₂).mono fun _ h₃ => WP.seq ((first_input hp h₃).mono fun _ h₄ =>
      first_finish hp h₄))))

end

end VG.Proof.Argon2.X86.HPrime

end

/-!
# Argon2 H′ on x86 (32-bit): the chain of 64-byte hashes

`chain_ok`: after the first prefix V₁[0, 32) of a long output, each iteration
hashes the digest again and emits the prefix of the new one, while more than
64 bytes are left. The output is then V₁[0, 32) ‖ `chainPrefixes j V₁` and the
digest `chainDigest j V₁`, with 33 to 64 bytes left.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (next emitPrefix cmpLeft chain leftOff)
open VG.Proof.Sha256.X86.Stream (Upd Fupd wp_movi wp_movm wp_cmpi)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

theorem chainDigest_succ' (j : Nat) (v : List Byte) :
    chainDigest (j + 1) v = Spec.Argon2.H 64 (chainDigest j v) := by
  induction j generalizing v with
  | zero => rfl
  | succ j ih => exact ih (Spec.Argon2.H 64 v)

theorem chainPrefixes_succ' (j : Nat) (v : List Byte) :
    chainPrefixes (j + 1) v = chainPrefixes j v ++ (Spec.Argon2.H 64 (chainDigest j v)).take 32 := by
  induction j generalizing v with
  | zero => simp [chainPrefixes, chainDigest]
  | succ j ih =>
    rw [chainPrefixes, ih, chainPrefixes, chainDigest, List.append_assoc]

theorem finalHash_length (h0 : HashValue 64) (d : List Byte) : (finalHash b h0 d).length = 64 := by
  simp only [finalHash, Proof.Argon2.wordList_length, Vector.length_toList]

/-- The output after `j` iterations. -/
abbrev chainOut (V : List Byte) (j : Nat) : List Byte := V.take 32 ++ chainPrefixes j V

theorem chainOut_length {V : List Byte} (hV : V.length = 64) (j : Nat) :
    (chainOut V j).length = 32 + 32 * j := by
  simp only [chainOut, List.length_append, List.length_take, hV, Proof.Argon2.chainPrefixes_length]
  omega_arith

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- `cmpLeft`: CF is whether fewer than 65 bytes are left. -/
theorem cmp_ok {s : State} (b : Body s₀ s) {xs : List Byte} (o : Out s₀ s xs) :
    WP isa (.block cmpLeft) s fun t => t.cf = some (decide (ol s₀ - xs.length < 65)) ∧
      Keeps (scr s₀) (esp₀ s₀) s t ∧ t.mem = s.mem := by
  have hs := hp.scr_fits
  obtain hol : ol s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  unfold cmpLeft
  obtain rl : InRegions (s.rd ++ s.wr) (addr (scr s₀) leftOff) 4 := by
    rw [b.rd, b.wr]
    exact ⟨scrR s₀, by simp [hp.wr], Proof.Sha256.X86.Stream.contains_addr (by decide) (by decide) hs⟩
  refine wp_movm (VG.Proof.Sha512.X86.ea_of b.ebx leftOff) rl fun s₁ u₁ =>
    wp_cmpi fun s₂ f₂ cf₂ _ => WP.block_nil ⟨?_, ?_, by rw [f₂.mem, u₁.mem]⟩
  · rw [cf₂, u₁.gpr, o.left, Proof.Sha256.X86.Stream.toNat_ofNat_lt (by omega_arith)]; rfl
  · exact Keeps.same (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.gpr, u₁.other _ (by decide)])
      (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.mem, u₁.mem]) (by rw [f₂.rd, u₁.rd])
      (by rw [f₂.wr, u₁.wr])

/-- What the chain keeps between iterations. -/
structure ChainInv (s₀ : State) (e : BitVec 32) (V : List Byte) (j : Nat) (s : State) : Prop where
  body : Body s₀ s
  ebp : s.gpr .ebp = e
  out : Out s₀ s (chainOut V j)
  digest : digest s₀ s = chainDigest j V

/-- One iteration. -/
theorem iter_ok {e : BitVec 32} {V : List Byte} (hV : V.length = 64) {j : Nat} {s : State}
    (h : ChainInv s₀ e V j s) (hl : 32 + 32 * j + 32 ≤ ol s₀) :
    WP isa (.seq (.block [.mov .edx (.imm 64)]) (.seq next (.seq emitPrefix (.block cmpLeft)))) s
      fun t => ChainInv s₀ e V (j + 1) t ∧
        t.cf = some (decide (ol s₀ - (32 + 32 * (j + 1)) < 65)) := by
  refine WP.seq (wp_movi fun s₁ u₁ => WP.block_nil ?_)
  obtain k₁ : Keeps (scr s₀) (esp₀ s₀) s s₁ := Keeps.same (u₁.other _ (by decide)) (u₁.other _ (by decide))
    (u₁.other _ (by decide)) u₁.mem u₁.rd u₁.wr
  obtain b₁ := h.body.keeps hp k₁
  refine WP.seq ((next_ok (b₁.ctx hp) (n := 64) u₁.gpr (by decide) (by decide)).mono
    fun s₂ ⟨d₂, k₂⟩ => ?_)
  obtain K₂ := k₁.trans k₂
  obtain b₂ := h.body.keeps hp K₂
  obtain o₂ := h.out.keeps hp K₂
  obtain hlen := chainOut_length hV j
  refine WP.seq ((emit_ok hp b₂ o₂ (by rw [hlen]; exact hl)).mono fun s₃ ⟨b₃, e₃, o₃, d₃⟩ => ?_)
  obtain dg : digest s₀ s₂ = chainDigest (j + 1) V := by
    rw [chainDigest_succ', ← h.digest, Proof.Argon2.H_stream,
      List.take_of_length_le (by rw [finalHash_length])]
    rw [u₁.mem] at d₂
    exact d₂
  obtain xs₃ : chainOut V j ++ (digest s₀ s₂).take 32 = chainOut V (j + 1) := by
    rw [dg, chainDigest_succ', chainOut, chainOut, chainPrefixes_succ', List.append_assoc]
  rw [xs₃] at o₃
  refine (cmp_ok hp b₃ o₃).mono fun t ⟨cf, k, m⟩ => ⟨⟨b₃.keeps hp k, ?_, o₃.keeps hp k, ?_⟩, ?_⟩
  · rw [k.ebp, e₃, K₂.ebp, h.ebp]
  · show bytesAt _ _ _ = _
    rw [m]
    exact d₃.trans dg
  · rw [cf, chainOut_length hV]

/-- The chain: iterations while more than 64 bytes are left. -/
theorem chain_ok {e : BitVec 32} {V : List Byte} (hV : V.length = 64) {j : Nat} {s : State}
    (h : ChainInv s₀ e V j s) (hl : 65 ≤ ol s₀ - (32 + 32 * j)) :
    WP isa chain s fun t => ∃ j', ChainInv s₀ e V j' t ∧ 33 ≤ ol s₀ - (32 + 32 * j') ∧
      ol s₀ - (32 + 32 * j') ≤ 64 ∧ 32 + 32 * j' ≤ ol s₀ := by
  unfold chain
  refine WP.loop (M := isa) (fun (m : Nat) (t : State) => ∃ j', m = ol s₀ - (32 + 32 * j') ∧ ChainInv s₀ e V j' t ∧ 65 ≤ m)
    ?_ (ol s₀ - (32 + 32 * j)) s ⟨j, rfl, h, hl⟩
  rintro m t ⟨j', rfl, hi, hm⟩
  refine (iter_ok hp hV hi (by omega_arith)).mono fun u ⟨hu, cf⟩ => ?_
  by_cases hc : ol s₀ - (32 + 32 * (j' + 1)) < 65
  · refine .inl ⟨?_, j' + 1, hu, by omega_arith, by omega_arith, by omega_arith⟩
    show u.cf.map (!·) = some false
    rw [cf]; simp [hc]
  · refine .inr ⟨?_, _, by omega_arith, j' + 1, rfl, hu, by omega_arith⟩
    show u.cf.map (!·) = some true
    rw [cf]; simp [hc]

end

end VG.Proof.Argon2.X86.HPrime

end

/-!
# Argon2 H′ on x86 (32-bit): the output from the first digest

`finish_ok`: `finishOutput` writes H′ to the output, from the first digest:
the digest itself for at most 64 bytes, and otherwise its prefix, the chain
and the last hash (`extend_ok`), of the 33 to 64 bytes left.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (next emitPrefix cmpLeft chain extendDigest finishOutput leftOff)
open VG.Proof.Sha256.X86.Stream (Upd wp_movm)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- What the chain leaves: the output after `j` iterations and the last hash. -/
def Extended (s₀ : State) (e : BitVec 32) (V : List Byte) (t : State) : Prop :=
  ∃ j, Body s₀ t ∧ t.gpr .ebp = e ∧ Out s₀ t (chainOut V j) ∧
    (digest s₀ t).take (ol s₀ - (32 + 32 * j)) =
      Spec.Argon2.H (ol s₀ - (32 + 32 * j)) (chainDigest j V) ∧
    33 ≤ ol s₀ - (32 + 32 * j) ∧ ol s₀ - (32 + 32 * j) ≤ 64 ∧ 32 + 32 * j ≤ ol s₀

theorem extend_ok {s : State} (b : Body s₀ s) (o : Out s₀ s []) (hol : 65 ≤ ol s₀) :
    WP isa extendDigest s (Extended s₀ (s.gpr .ebp) (digest s₀ s)) := by
  have hs := hp.scr_fits
  obtain hV : (digest s₀ s).length = 64 := by simp [digest, bytesAt]
  unfold extendDigest
  refine WP.seq ((emit_ok hp b o (by simp only [List.length_nil]; omega_arith)).mono
    fun s₁ ⟨b₁, e₁, o₁, d₁⟩ => ?_)
  rw [List.nil_append, show (digest s₀ s).take 32 = chainOut (digest s₀ s) 0 by
    simp [chainOut, chainPrefixes]] at o₁
  obtain i₁ : ChainInv s₀ (s.gpr .ebp) (digest s₀ s) 0 s₁ := ⟨b₁, e₁, o₁, d₁⟩
  refine WP.seq ((cmp_ok hp b₁ o₁).mono fun s₂ ⟨cf₂, k₂, m₂⟩ => ?_)
  rw [chainOut_length hV] at cf₂
  obtain i₂ : ChainInv s₀ (s.gpr .ebp) (digest s₀ s) 0 s₂ :=
    ⟨b₁.keeps hp k₂, k₂.ebp.trans e₁, o₁.keeps hp k₂, by show bytesAt _ _ _ = _; rw [m₂]; exact d₁⟩
  obtain hIte : WP isa (.ite .b (.block []) chain) s₂ fun t => ∃ j, ChainInv s₀ (s.gpr .ebp) (digest s₀ s) j t ∧
      33 ≤ ol s₀ - (32 + 32 * j) ∧ ol s₀ - (32 + 32 * j) ≤ 64 ∧ 32 + 32 * j ≤ ol s₀ := by
    refine WP.ite (decide (ol s₀ - (32 + 32 * 0) < 65)) cf₂ (fun h => WP.block_nil ⟨0, i₂, ?_⟩)
      (fun h => (chain_ok hp hV i₂ ?_).mono fun t h => h)
    · simp only [decide_eq_true_eq] at h; omega_arith
    · simp only [decide_eq_false_iff_not] at h; omega_arith
  refine WP.seq (hIte.mono fun s₃ ⟨j, i₃, l₁, l₂, l₃⟩ => ?_)
  obtain rl : InRegions (s₃.rd ++ s₃.wr) (addr (scr s₀) leftOff) 4 := by
    rw [i₃.body.rd, i₃.body.wr]
    exact ⟨scrR s₀, by simp [hp.wr], Proof.Sha256.X86.Stream.contains_addr (by decide) (by decide) hs⟩
  refine WP.seq (wp_movm (VG.Proof.Sha512.X86.ea_of i₃.body.ebx leftOff) rl fun s₄ u₄ => WP.block_nil ?_)
  obtain k₄ : Keeps (scr s₀) (esp₀ s₀) s₃ s₄ := Keeps.same (u₄.other _ (by decide)) (u₄.other _ (by decide))
    (u₄.other _ (by decide)) u₄.mem u₄.rd u₄.wr
  obtain b₄ := i₃.body.keeps hp k₄
  obtain edx₄ : s₄.gpr .edx = BitVec.ofNat 32 (ol s₀ - (32 + 32 * j)) := by
    rw [u₄.gpr, i₃.out.left, chainOut_length hV]
  refine (next_ok (b₄.ctx hp) edx₄ (by omega_arith) l₂).mono fun t ⟨d, k⟩ => ?_
  obtain K := k₄.trans k
  refine ⟨j, i₃.body.keeps hp K, by rw [K.ebp, i₃.ebp], i₃.out.keeps hp K, ?_, l₁, l₂, l₃⟩
  rw [Proof.Argon2.H_stream, ← i₃.digest]
  rw [u₄.mem] at d
  exact congrArg (List.take _) d

/-- `finishOutput` writes H′ of the input `I` from its first digest. -/
theorem finish_ok {s : State} (b : Body s₀ s) (o : Out s₀ s []) {I : List Byte}
    (hd : (digest s₀ s).take (min (ol s₀) 64) =
      Spec.Argon2.H (min (ol s₀) 64) (Spec.Argon2.le32 (ol s₀) ++ I)) :
    WP isa finishOutput s fun t => Body s₀ t ∧ t.gpr .ebp = s.gpr .ebp ∧
      bytesAt t.mem ((op s₀).setWidth 64) (ol s₀) = Spec.Argon2.hPrime (ol s₀) I := by
  have hpos := hp.ol_pos
  obtain hV : (digest s₀ s).length = 64 := by simp [digest, bytesAt]
  unfold finishOutput
  refine WP.seq ((cmp_ok hp b o).mono fun s₁ ⟨cf₁, k₁, m₁⟩ => ?_)
  simp only [List.length_nil, Nat.sub_zero] at cf₁
  obtain b₁ := b.keeps hp k₁
  obtain o₁ := o.keeps hp k₁
  obtain d₁ : digest s₀ s₁ = digest s₀ s := by show bytesAt _ _ _ = _; rw [m₁]
  obtain hIte : WP isa (.ite .b (.block []) extendDigest) s₁ fun t => Body s₀ t ∧ t.gpr .ebp = s.gpr .ebp ∧
      ∃ xs, Out s₀ t xs ∧ xs.length < ol s₀ ∧ ol s₀ - xs.length ≤ 64 ∧
        xs ++ (digest s₀ t).take (ol s₀ - xs.length) = Spec.Argon2.hPrime (ol s₀) I := by
    refine WP.ite (decide (ol s₀ < 65)) cf₁ (fun h => WP.block_nil ?_) (fun h => ?_)
    · simp only [decide_eq_true_eq] at h
      refine ⟨b₁, k₁.ebp, [], o₁, by simp only [List.length_nil]; omega_arith,
        by simp only [List.length_nil]; omega_arith, ?_⟩
      rw [Nat.min_eq_left (by omega_arith)] at hd
      rw [List.nil_append, List.length_nil, Nat.sub_zero, d₁, hd]
      simp only [Spec.Argon2.hPrime, eq_true (by omega_arith : ol s₀ ≤ 64), ite_true]
    · simp only [decide_eq_false_iff_not] at h
      refine (extend_ok hp b₁ o₁ (by omega_arith)).mono fun t ⟨j, bt, et, ot, dt, l₁, l₂, l₃⟩ =>
        ⟨bt, et.trans k₁.ebp, _, ot, ?_, ?_, ?_⟩
      · rw [chainOut_length (by rw [d₁]; exact hV)]; omega_arith
      · rw [chainOut_length (by rw [d₁]; exact hV)]; omega_arith
      · have V₁ : digest s₀ s₁ = Spec.Argon2.H 64 (Spec.Argon2.le32 (ol s₀) ++ I) := by
          rw [d₁, ← List.take_of_length_le (l := digest s₀ s) (i := 64) (by rw [hV]),
            ← Nat.min_eq_right (by omega_arith : 64 ≤ ol s₀), hd]
        rw [chainOut_length (by rw [d₁]; exact hV), dt, chainOut, ← Proof.Argon2.longHash_chain, V₁]
        obtain hr : (ol s₀ + 31) / 32 - 2 = j + 1 := by omega_arith
        simp only [Spec.Argon2.hPrime, eq_false (by omega_arith : ¬ ol s₀ ≤ 64), ite_false]
        rw [hr, show ol s₀ - 32 * (j + 1) = ol s₀ - (32 + 32 * j) by omega_arith]
  refine WP.seq (hIte.mono fun s₂ ⟨b₂, e₂, xs, o₂, l₁, l₂, h₂⟩ => ?_)
  refine (copyRemaining_ok hp b₂ o₂ l₁ l₂).mono fun t ⟨bt, et, ht⟩ => ⟨bt, et.trans e₂, ?_⟩
  rw [ht, h₂]

end

end VG.Proof.Argon2.X86.HPrime
