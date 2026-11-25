module

public import VerifiedGarbage.Impl.Weierstrass.AArch64
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn
public import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Proof.Mont.AArch64.P521
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block

/-!
# P-521's field products as functions, and calls of them, on AArch64

The functions (`Impl/Weierstrass/AArch64/P521.lean`) are the bodies of
`Proof/Mont/AArch64/P521.lean` in the entry and exit of the other functions
(`mulFnOf_ok`); `fieldCall521_ok` is a call of one, as the inline product.
-/

-- separate module: the functions' calls, apart from the field programs that make them
@[expose] public section

set_option exponentiation.threshold 1024

namespace VG.Proof.Weierstrass.AArch64.Mont

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass.AArch64.Mont
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521 (prime)
open VG.Proof.Ed25519.AArch64 (Keeps)

private theorem storesR_novec (rn : Reg) : ∀ (ts : List Reg) (o : Nat), ∀ i ∈ storesR rn ts o, vdstOf i = none
  | [], _, _, h => absurd h (by simp [storesR])
  | t :: ts, o, i, h => by
    rw [storesR] at h
    rcases List.mem_cons.mp h with rfl | h
    · rfl
    · exact storesR_novec rn ts (o + 8) i h

private theorem code_novec (ra rb : Reg) (a b : Nat) (os : List Impl.Mont.AArch64.P521.Op) :
    ∀ i ∈ Impl.Mont.AArch64.P521.code ra rb a b os, vdstOf i = none := by
  intro i h
  obtain ⟨o, -, rfl⟩ := List.mem_map.mp h
  cases o <;> rfl

private theorem clob_bodyW : ∀ r ∈ clob 9, r ∈ bodyW 9 := by decide

private theorem prodBody_ok {s : State} {base : Addr} {size : Nat} (_ : Scr s base size) {pa pb po : Addr}
    (hpa : Ptr s (raF 9) pa (8 * 9)) (hpb : Ptr s .x3 pb (8 * 9)) (hpo : PtrW s (roF 9) po (8 * 9))
    (hAB : wordsVal s.mem pa 0 9 < prime ∧ wordsVal s.mem pb 0 9 < prime) :
    WP isa (.block P521.prodBody) s fun s' =>
      (∀ r, r ∉ bodyW 9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Outside po 0 (8 * 9) s.mem s'.mem ∧ wordsVal s'.mem po 0 9 < prime ∧
      wordsVal s'.mem po 0 9 * 2 ^ (64 * 9) % prime = wordsVal s.mem pa 0 9 * wordsVal s.mem pb 0 9 % prime := by
  rw [P521.prodBody]
  refine WP.block_cons_iff.mpr ⟨_, exec_addImm_x (show 0 < 4096 by decide), ?_⟩
  have k : Keeps [.x27] s (s.write .x .x27 (s.gpr .x3 + BitVec.ofNat 64 0)) :=
    ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl, rfl⟩
  have hpb' : Ptr (s.write .x .x27 (s.gpr .x3 + BitVec.ofNat 64 0)) .x27 pb (8 * 9) :=
    ⟨by rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero]; exact hpb.reg, hpb.ld, hpb.enc⟩
  refine WP.mono (Mont.AArch64.P521.mulR_ok (hpa.of_keeps k (by decide)) hpb' (hpo.of_keepRegs (Keeps.regs k) (by decide))
    (by decide) (by decide) (by decide) (o := 0) (a := 0) (b := 0) (by decide) (by decide) (by decide) rfl rfl rfl hAB.1 hAB.2)
    fun t ⟨K, hlt, he⟩ => ⟨fun r hr => ?_, K.rd, K.wr, K.sp, K.mem, hlt, he⟩
  rw [K.gpr r fun h => hr (clob_bodyW r h)]
  exact k.gpr r fun h => hr (by rw [List.mem_singleton.mp h]; decide)

private theorem sqrBody_ok {s : State} {base : Addr} {size : Nat} (_ : Scr s base size) {pa pb po : Addr}
    (hpa : Ptr s (raF 9) pa (8 * 9)) (_ : Ptr s .x3 pb (8 * 9)) (hpo : PtrW s (roF 9) po (8 * 9))
    (hA : wordsVal s.mem pa 0 9 < prime) :
    WP isa (.block P521.sqrBody) s fun s' =>
      (∀ r, r ∉ bodyW 9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Outside po 0 (8 * 9) s.mem s'.mem ∧ wordsVal s'.mem po 0 9 < prime ∧
      wordsVal s'.mem po 0 9 * 2 ^ (64 * 9) % prime = wordsVal s.mem pa 0 9 * wordsVal s.mem pa 0 9 % prime :=
  WP.mono (Mont.AArch64.P521.sqrR_ok hpa hpo (by decide) (by decide) (o := 0) (a := 0) (by decide) (by decide) rfl rfl hA)
    fun _ ⟨K, hlt, he⟩ => ⟨fun r hr => K.gpr r fun h => hr (clob_bodyW r h), K.rd, K.wr, K.sp, K.mem, hlt, he⟩

private theorem fn_wp (body : List Instr) {s : State} {Q : State → Prop} : WP isa (P521.fn body) s Q ↔
    WP isa (.block (zextCode ++ (saveCode 9 ++ (ptrsCode 9 ++ (body ++ restoreCode 9))))) s Q := by
  rw [P521.fn, WP.seq_iff, ← WP.block_append_iff]
  simp only [ptrsCode, raF, roF, Nat.reduceLeDiff, ite_false, List.append_assoc]

/-- A call of P-521's product or square, as the inline product. -/
theorem fieldCall521_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkA M size m s.mem base) (hf : P521.isField M.n m = true) (htmp : M.tmp = moAt M.n) {o a b : Nat}
    (ho : o + 8 * M.n ≤ own M.n) (ha : a + 8 * M.n ≤ own M.n) (hb : b + 8 * M.n ≤ own M.n)
    (hA : wordsVal s.mem base a M.n < m) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (fieldCall521 o a b) s fun s' => OpKeep M base o s s' ∧ wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  simp only [P521.isField, Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨hn, rfl⟩ := hf
  rw [fieldCall521]
  split
  · rename_i hab
    obtain rfl := beq_iff_eq.mp hab
    refine callProg_ok hs hM (.inr (.inr (.inr (.inr hn)))) htmp ho ha ha (code := P521.sqrFn) rfl (fun A _ => A < prime) (fun A _ => A * A) hA
      fun {W t} hp hA => ?_
    rw [hn] at hp hA ⊢
    rw [P521.sqrFn, fn_wp]
    exact mulFnOf_ok (n := 9) (.inr rfl) (fun A _ => A < prime) (fun A _ => A * A)
      (fun i hi => (List.mem_append.mp hi).elim (code_novec _ _ _ _ _ i) (storesR_novec _ _ _ i)) sqrBody_ok hp hA
  · refine callProg_ok hs hM (.inr (.inr (.inr (.inr hn)))) htmp ho ha hb (code := P521.prodFn) rfl (fun A B => A < prime ∧ B < prime) (· * ·)
      ⟨hA, hB⟩ fun {W t} hp hAB => ?_
    rw [hn] at hp hAB ⊢
    rw [P521.prodFn, fn_wp]
    refine mulFnOf_ok (n := 9) (.inr rfl) (fun A B => A < prime ∧ B < prime) (· * ·) (fun i hi => ?_) prodBody_ok hp hAB
    rcases List.mem_cons.mp hi with rfl | hi
    · rfl
    · exact (List.mem_append.mp hi).elim (code_novec _ _ _ _ _ i) (storesR_novec _ _ _ i)

end VG.Proof.Weierstrass.AArch64.Mont
