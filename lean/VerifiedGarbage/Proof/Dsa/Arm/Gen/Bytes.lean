module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.St
public import VerifiedGarbage.Proof.Rsa.Arm.RvVP
import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: pointers into `scratch` and copies

`scr_ok`: `scr L d o` sets `d` to `scratch + o`, from `r8`. `copyS_vp`:
a copy between two ranges of `scratch`, as a piece (`VP`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_movw wp_dp op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- Equal reads are equal bytes. -/
theorem bytesAt_of_read {m m' : Mem} {a b : Addr} {n : Nat} (h : m'.read a n = m.read b n) :
    Spec.Rsa.bytesAt m' a n = Spec.Rsa.bytesAt m b n := by
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [← Mem.extractLsb'_read m' a hi, ← Mem.extractLsb'_read m b hi, h]

theorem bytesAt_length' (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

/-- `KB - (sK - o) = scratch + o`. -/
theorem kb_sub (G : GP) {o : Nat} (ho : o ≤ sK G.pLen) (h16 : sK G.pLen - o < 2 ^ 16) :
    G.KB - (BitVec.ofNat 16 (sK G.pLen - o)).setWidth 32 = G.scr + BitVec.ofNat 32 o := by
  have e : (BitVec.ofNat 16 (sK G.pLen - o)).setWidth 32 = BitVec.ofNat 32 (sK G.pLen - o) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  rw [e, GP.KB]
  obtain ⟨d, hd⟩ : ∃ d, sK G.pLen = d + o := ⟨sK G.pLen - o, by omega⟩
  rw [hd, Nat.add_sub_cancel, BitVec.ofNat_add,
    show G.scr + (BitVec.ofNat 32 d + BitVec.ofNat 32 o) = G.scr + BitVec.ofNat 32 o + BitVec.ofNat 32 d by
      ac_rfl, BitVec.add_sub_cancel]

/-- `sK` fits a `movw`. -/
theorem sK_lt {L : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) : sK L < 2 ^ 16 := by
  simp only [sK, sA, wa]; rcases hL with rfl | rfl | rfl <;> decide

section
variable {G : GP}

/-- `scr L d o`: `d := scratch + o`. -/
theorem scr_ok {s : State} {L o : Nat} {d : Reg} (r8 : s.gpr .r8 = G.KB) (hL : L = G.pLen)
    (hLv : L = 128 ∨ L = 256 ∨ L = 384) (ho : o ≤ sK L) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr d = G.scr + BitVec.ofNat 32 o → Rest [.r12, d] s t → t.mem = s.mem →
      WP isa (.block rest) t Q) :
    WP isa (.block (scr L d o ++ rest)) s Q := by
  subst hL
  have := sK_lt hLv
  simp only [scr, List.cons_append, List.nil_append]
  refine wp_movw fun s₁ u₁ => wp_dp (op2_reg _ _) fun t u₂ => k t ?_
    ((u₁.rest (by simp)).trans (u₂.rest (by simp))) (by rw [u₂.mem, u₁.mem])
  rw [u₂.gpr, dpVal, u₁.gpr, u₁.other .r8 (by decide), r8]
  exact kb_sub G ho (by omega)

/-- The taint certificate of a piece whose addresses come from `r8`, from
its hint on one instance: the analysis looks at no immediate. -/
abbrev Cert8 (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8]) c hc).isSome = true

theorem copyS_cert (L dst src n : Nat) : Cert8 (copyS L dst src n) :=
  ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8]) (copyS 128 0 64 5), rfl⟩

/-- The range `[o, o + n)` of `scratch`, below the key working space. -/
theorem SS.addr {σ s : State} {c : Cfg} (h : SS G σ c s) {o n : Nat} (ho : o + n ≤ sK G.pLen) (hn : 0 < n) :
    State.addr (G.scr + BitVec.ofNat 32 o) = G.sa o := by
  have := h.gi.scrBig; exact h.gi.saddr (by omega)

theorem SS.toNat {σ s : State} {c : Cfg} (h : SS G σ c s) {o : Nat} (ho : o ≤ sK G.pLen) :
    (G.scr + BitVec.ofNat 32 o).toNat = G.scr.toNat + o := by
  have := h.gi.scrBig; have := h.gi.scrFit
  have : 0 < kz G.pLen := by simp only [kz]; omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : o < 2 ^ 32)]
  exact Nat.mod_eq_of_lt (by omega)

/-- A copy between two ranges of `scratch` below the key working space. -/
theorem copyS_vp {F Q : State → State → Prop} {c : State → Cfg} {L dst src n : Nat}
    (hF : ∀ σ s, F σ s → SS G σ (c σ) s) (hL : L = G.pLen) (hn : 0 < n) (hn16 : n < 2 ^ 16)
    (hd : dst + n ≤ sK L) (hsr : src + n ≤ sK L) (hsep : dst + n ≤ src ∨ src + n ≤ dst)
    (k : ∀ σ s t, F σ s → Rest [.r0, .r1, .r2, .r12, .lr] s t → Frame [G.rs dst n] s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa dst) n = Spec.Rsa.bytesAt s.mem (G.sa src) n → Q σ t) :
    VP F (copyS L dst src n) Q := by
  refine VP.taint [.r8] (copyS_cert L dst src n) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s hs => ?_
  · simp only [List.mem_singleton] at hr; subst hr; rw [(hF _ _ h₁).r8, (hF _ _ h₂).r8]
  have h := hF σ s hs
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have hLv := h.lens
  subst hL
  simp only [copyS, copyN, List.append_assoc]
  refine WP.seq (scr_ok (d := .r1) h.r8 rfl hLv (by omega) fun s₁ v₁ R₁ M₁ => ?_)
  refine scr_ok (d := .r0) (by rw [R₁.gpr _ (by decide)]; exact h.r8) rfl hLv (by omega) fun s₂ v₂ R₂ M₂ => ?_
  refine wp_movw fun s₃ u₃ => WP.block_nil ?_
  have R : Rest [.r0, .r1, .r2, .r12, .lr] s s₃ :=
    ((R₁.mono (by simp)).trans (R₂.mono (by simp))).trans (u₃.rest (by simp))
  have M : s₃.mem = s.mem := by rw [u₃.mem, M₂, M₁]
  have ad := h.addr hd hn
  have as := h.addr hsr hn
  refine WP.mono (VG.Proof.Bignum.Arm.copyBuffer_ok s₃ (src := G.scr + BitVec.ofNat 32 src)
    (dst := G.scr + BitVec.ofNat 32 dst) hn (by rw [h.toNat (by omega)]; omega)
    (by rw [h.toNat (by omega)]; omega) (by omega)
    (by rw [as, R.rd, R.wr]
        obtain ⟨r, hr, hc⟩ := gi.inScr (o := src) (n := n) (by omega)
        exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [ad, R.wr]; exact gi.inScr (by omega))
    (by rw [as, ad]; exact gi.sdisj (by omega) (by omega) (by omega))
    (by rw [u₃.other .r0 (by decide)]; exact v₂)
    (by rw [u₃.other .r1 (by decide), R₂.gpr .r1 (by decide)]; exact v₁)
    (by rw [u₃.gpr]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega))
    fun t ⟨rd, fr, _, rest⟩ => k σ s t hs (R.trans (rest.mono (by simp)))
      (by rw [← M]; show Frame [⟨G.sa dst, n⟩] _ _; rw [← ad]; exact fr) ?_
  rw [← as, ← ad, ← M]; exact bytesAt_of_read rd

end

end VG.Proof.Dsa.Arm.Gen
