module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PrivPreC
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# An RSA private key's precomputed values on PPC64LE: the modulus

`partC_ok`: after the factors (`B`), `n`'s values to `pre`
(`Precompute.core`), then and-ed with the mask, and the result.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.PrivPre

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- `maskN`'s loop: the `w` words at `r14` (`P`) `&=` the mask of `b`. -/
theorem maskIn_ok {s : State} {P : Addr} {L w : Nat} {b : Bool} (hp : Scr s P L)
    (h14 : s.gpr .r14 = off P 0) (h17 : s.gpr .r17 = BitVec.ofNat 64 w) (h26 : s.gpr .r26 = Crt.bmask b)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hL : 8 * w ≤ L) :
    WP isa (Precompute.countLoop .r17 [.load .d .r0 .r14 0, .logic .and .r0 .r0 .r26, .store .d .r0 .r14 0,
      .addi .r14 .r14 8]) s fun t =>
      ((∀ i < w, word t.mem P (8 * i) = if b then word s.mem P (8 * i) else 0) ∧
        Outside P 0 (8 * w) s.mem t.mem) ∧ Keep [.r0, .r14, .r17] s t := by
  have hnP := hp.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off P (8 * i) ∧ t.gpr .r26 = Crt.bmask b ∧
      (∀ j < i, word t.mem P (8 * j) = if b then word s.mem P (8 * j) else 0) ∧
      (∀ j, i ≤ j → j < w → word t.mem P (8 * j) = word s.mem P (8 * j)) ∧
      Outside P 0 (8 * i) s.mem t.mem ∧ Keep [.r0, .r14, .r17] s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .r0 .r14 0, .logic .and .r0 .r0 .r26,
      .store .d .r0 .r14 0, .addi .r14 .r14 8] ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := w) (by omega_arith) (by omega_arith) Inv (fun i hi t ⟨j14, j26, jw, jr, jout, jk⟩ _ => ?_)
    ⟨by rw [h14], h26, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl, Outside.refl _ _ _ _,
      (Keep.refl [] s).mono (by decide)⟩ h17)
    fun t ⟨_, _, tw, _, tout, tk⟩ => ⟨⟨tw, tout⟩, tk⟩
  have hst : WP isa (.block [.load .d .r0 .r14 0, .logic .and .r0 .r0 .r26, .store .d .r0 .r14 0,
      .addi .r14 .r14 8, .subi .r17 .r17 1]) t fun t' =>
      (t'.gpr .r14 = off P (8 * i + 8) ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off P (8 * i)) (word t.mem P (8 * i) &&& Crt.bmask b)) ∧
      Keep [.r0, .r14, .r17] t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [j14, j26, (hp.congr jk.wr).ld (show 8 * i + 8 ≤ L by omega_arith),
      (hp.congr jk.wr).st (show 8 * i + 8 ≤ L by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l14, l17, lm⟩, lk⟩ => ⟨⟨?_, (lk.gpr _ (by decide)).trans j26, fun j hj => ?_,
    fun j hj hj' => ?_, ?_, jk.trans' lk⟩, l17⟩
  · rw [l14, show 8 * i + 8 = 8 * (i + 1) by omega_arith]
  · rw [lm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [(writeW_outside t.mem P (d := 8 * i) _ (by omega_arith)).word (by omega_arith) (by omega_arith), jw j hj]
    · rw [word_writeW_self, jr j (Nat.le_refl _) hi, PrivPre.and_bmask]
  · rw [lm, (writeW_outside t.mem P (d := 8 * i) _ (by omega_arith)).word (by omega_arith) (by omega_arith),
      jr j (by omega_arith) hj']
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside _ P (d := 8 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))

/-- A load of the header's word at `o` (`r23`) into `rd`. -/
theorem ldH_ok {s : State} {S : Addr} {Z o : Nat} {rd : Reg} (hs : Scr s S Z) (h23 : s.gpr .r23 = S)
    (ho : o + 8 ≤ Z) (ho' : o < 2 ^ 15 ∧ o % 4 = 0) :
    WP isa (.block [.load .d rd .r23 o]) s fun t =>
      (t.gpr rd = word s.mem S o ∧ t.mem = s.mem) ∧ Keep [rd] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r23 ≠ .r0 by decide) ho' (by rw [h23]; exact hs.ld ho), Option.some.injEq,
    exists_eq_left', h23]
  exact ⟨⟨by simp [gpr_write], rfl⟩, Keep.write _ _ _⟩

/-- The registers `setupN` writes. -/
def nRegs : List Reg := [.r19, .r12, .r6, .r21, .r11, .r4, .r10, .r5, .r8, .r9]

/-- `setupN`, after the factors: `Precompute.core`'s registers. -/
theorem setupN_ok {s₀ u : State} (hP : PF s₀) (hB : B s₀ u) :
    WP isa (.block PrivPre.setupN) u fun v =>
      (v.gpr .r19 = s₀.gpr .r3 ∧ v.gpr .r12 = s₀.gpr .r5 ∧ v.gpr .r6 = BitVec.ofNat 64 (ck s₀) ∧
        v.gpr .r21 = cS s₀ ∧ v.gpr .r11 = BitVec.ofNat 64 (2 * cw s₀) ∧
        v.gpr .r10 = off (cS s₀) (slot (cw s₀) 0) ∧ v.gpr .r5 = off (cS s₀) (slot (cw s₀) 1) ∧
        v.gpr .r8 = off (cS s₀) (slot (cw s₀) 2) ∧ v.gpr .r9 = off (cS s₀) (slot (cw s₀) 3) ∧ v.mem = u.mem) ∧
      Keep nRegs u v := by
  have hn := hP.nw
  have room := hP.room
  have k64 := hP.k64; have k1024 := hP.k1024
  rw [show PrivPre.setupN = [.load .d .r19 .r23 oOut] ++ ([.load .d .r12 .r23 oN] ++ ([.load .d .r6 .r23 oNLen] ++
    [.addi .r21 .r23 0, .addi .r11 .r6 7, .lsr .d .r11 .r11 3, .lsl .r4 .r11 3, .addi .r4 .r4 16,
      .addi .r10 .r21 hdrBytes, .add .r5 .r10 .r4, .add .r8 .r5 .r4, .add .r9 .r8 .r4, .lsl .r11 .r11 1])) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (ldH_ok hB.scr hB.r23 (by simp (config := { failIfUnchanged := false }) only [cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes, oOut] at *; omega_arith) (by decide)) fun u1 ⟨⟨a19, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldH_ok (hB.scr.congr k1.wr) ((k1.gpr _ (by decide)).trans hB.r23) (by simp (config := { failIfUnchanged := false }) only [cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes, oN] at *; omega_arith) (by decide))
    fun u2 ⟨⟨a12, m2⟩, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldH_ok (hB.scr.congr (k1.trans k2).wr) (((k1.trans k2).gpr _ (by decide)).trans hB.r23) (by simp (config := { failIfUnchanged := false }) only [cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes, oNLen] at *; omega_arith)
    (by decide)) fun u3 ⟨⟨a6, m3⟩, k3⟩ => ?_
  have k13 := (k1.trans k2).trans k3
  obtain ⟨K, hKe⟩ : ∃ K, ck s₀ = K := ⟨_, rfl⟩
  have e6 : u3.gpr .r6 = BitVec.ofNat 64 K := by
    rw [a6, m2, m1, hB.hNL, ← hKe]; exact (ofNat_toNat64 _).symm
  have e23 : u3.gpr .r23 = cS s₀ := (k13.gpr _ (by decide)).trans hB.r23
  refine WP.mono (WP.keep [.r21, .r11, .r4, .r10, .r5, .r8, .r9]
    (Q := fun v => v.gpr .r21 = cS s₀ ∧ v.gpr .r11 = BitVec.ofNat 64 (2 * cw s₀) ∧
      v.gpr .r10 = off (cS s₀) (slot (cw s₀) 0) ∧ v.gpr .r5 = off (cS s₀) (slot (cw s₀) 1) ∧
      v.gpr .r8 = off (cS s₀) (slot (cw s₀) 2) ∧ v.gpr .r9 = off (cS s₀) (slot (cw s₀) 3) ∧ v.mem = u3.mem) (by
        prun [e6, e23, BitVec.add_zero, Pre.ofNat_add7_shr3 K (by simp (config := { failIfUnchanged := false }) only [cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith), Pre.ofNat_shl3, Pre.ofNat_shl1, hdrBytes]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [off, slot, hdrBytes, BitVec.add_assoc, BitVec.ofNat_add_ofNat, cw, hKe] <;>
          (try congr 2) <;> omega_arith) (by decide))
    fun v ⟨⟨v21, v11, v10, v5, v8, v9, vm⟩, kv⟩ => ⟨⟨?_, ?_, ?_, v21, v11, v10, v5, v8, v9, by rw [vm, m3, m2, m1]⟩,
      (k13.trans kv).mono (by decide)⟩
  · rw [kv.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), a19, hB.hOut]
  · rw [kv.gpr _ (by decide), k3.gpr _ (by decide), a12, m1, hB.hN]
  · rw [kv.gpr _ (by decide), e6, hKe]

/-- A word of `pre` from `n`, after `core` (which writes `n`'s values in
`pre`'s first `n` bytes and arrays in the working space). -/
theorem core_word_pre {m m' : Mem} {P S : Addr} {n L Z PL d : Nat}
    (F : Frame [⟨off S hdrBytes, L⟩, ⟨P, n⟩] m m') (hsep : ∀ x, ofs P x < PL → Z ≤ ofs S x)
    (hd : n ≤ d) (hd' : d + 8 ≤ PL) (hZ : hdrBytes + L ≤ Z) (hnw : S.toNat + Z ≤ 2 ^ 64)
    (hPn : P.toNat + PL ≤ 2 ^ 64) : word m' P d = word m P d := by
  refine Mem.readW_congr fun i hi => F _ fun r hr hc => ?_
  have hx : ofs P (off P d + BitVec.ofNat 64 i) = d + i := by
    simp only [ofs, off]; rw [Offset.add_add, Mem.sub_ofNat_toNat _ (by omega_arith)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have := in_of_contains hc (by unfold hdrBytes; omega_arith) (by omega_arith)
    have := hsep (off P d + BitVec.ofNat 64 i) (by omega_arith)
    omega_arith
  · simp only [Region.Contains] at hc
    simp only [ofs] at hx
    omega_arith

/-- A word of the header, after `core`. -/
theorem core_word_hdr {m m' : Mem} {P S : Addr} {n L Z PL d : Nat}
    (F : Frame [⟨off S hdrBytes, L⟩, ⟨P, n⟩] m m') (hsep : ∀ x, ofs P x < PL → Z ≤ ofs S x)
    (hd : d + 8 ≤ hdrBytes) (hn : n ≤ PL) (hZ : hdrBytes + L ≤ Z) (hnw : S.toNat + Z ≤ 2 ^ 64) (hL0 : 0 < L) :
    word m' S d = word m S d := by
  refine Mem.readW_congr fun i hi => F _ fun r hr hc => ?_
  have hx : ofs S (off S d + BitVec.ofNat 64 i) = d + i := by
    simp only [ofs, off]; rw [Offset.add_add, Mem.sub_ofNat_toNat _ (by unfold hdrBytes at hd; omega_arith)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have := in_of_contains hc (by unfold hdrBytes; omega_arith) (by omega_arith)
    omega_arith
  · simp only [Region.Contains] at hc
    have := hsep (off S d + BitVec.ofNat 64 i) (by simp only [ofs]; omega_arith)
    unfold hdrBytes at hd hZ
    omega_arith

end VG.Proof.Bignum.PPC64LE.PrivPre
