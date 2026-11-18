module

public import VerifiedGarbage.Impl.CmacAes.AArch64.Aese
public import VerifiedGarbage.Proof.CmacAes.AArch64.UpdateLoop
public import VerifiedGarbage.Spec.Cmac.Contract
import VerifiedGarbage.Proof.CmacAes.AArch64.UpdateCorrect
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.CmacAes.AArch64.Aese
meta import VerifiedGarbage.Proof.CmacAes.AArch64.UpdateLoop
meta import VerifiedGarbage.Spec.Cmac.Contract
meta import VerifiedGarbage.Proof.CmacAes.AArch64.UpdateCorrect
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.CmacAes.AArch64.Subkeys
meta import VerifiedGarbage.Proof.CmacAes.AArch64.Subkeys
import VerifiedGarbage.Proof.CmacAes.AArch64.Finalize
meta import VerifiedGarbage.Proof.CmacAes.AArch64.Finalize

/-! ### `CmacAes.AArch64.Verified`, which this module and modules that import it used -/

section

/-! ### `CmacAes.AArch64.UpdateCT`, which this module and modules that import it used -/

section

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_update` is constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`): the taint analysis covers the code between the calls, from
the registers the correctness proof pins to the public arguments (`LInv`), and
each call of `vg_aes_ctr32` is constant time by its own proof (`ctr_rel`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- States agree on the registers `rs` and the stack pointer. -/
theorem agree_of {rs : List Reg} {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : VG.AArch64.Taint.Agree (Taint.ofRegs rs) s₁ s₂ :=
  ⟨hsp, fun r hr => h r (VG.AArch64.Taint.mem_ofRegs.mp hr)⟩

section
variable {s₀ s₀' : State} (hq : updateAArch64.pub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.1
theorem pub_x1 : s₀.gpr .x1 = s₀'.gpr .x1 := hq.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_x1 hq]
theorem pub_St : St s₀ = St s₀' := hq.2.2.1
theorem pub_Dp : Dp s₀ = Dp s₀' := hq.2.2.2.1
theorem pub_N : N s₀ = N s₀' := by rw [N, N, hq.2.2.2.2.1]
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.1
theorem pub_sp : s₀.sp = s₀'.sp := hq.2.2.2.2.2.2

/-- The registers the invariant pins agree in both runs. -/
theorem LInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : LInv s₀ k s₁) (h₂ : LInv s₀' k s₂) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x24]) s₁ s₂ := by
  refine agree_of (by rw [h₁.sp, h₂.sp, pub_sp hq]) fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.x19, h₂.x19, pub_W hq]
  · rw [h₁.x20, h₂.x20, pub_x1 hq]
  · rw [h₁.x21, h₂.x21, pub_St hq]
  · rw [h₁.x22, h₂.x22, pub_Dp hq]
  · rw [h₁.x23, h₂.x23, pub_N hq]
  · rw [h₁.x24, h₂.x24, pub_S hq]

end

/-! ## One block -/

/-- What is known between the code before the call and the call. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  pre : CallPre s (W s₀) (S s₀ + BitVec.ofNat 64 2048) (St s₀) (S s₀) (R s₀)
  x22 : s.gpr .x22 = Dp s₀ + BitVec.ofNat 64 (16 * k)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (N s₀ - k)
  sp : s.sp = s₀.sp

theorem bodyMid_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa (.block (chainIn ++ updArgs)) s (Mid s₀ k) :=
  WP.mono (bodyA_wp hp hk h) fun _ hb =>
    ⟨hb.pre, by rw [hb.saved .x22 (by simp [preserved]), h.x22],
      by rw [hb.saved .x23 (by simp [preserved]), h.x23], by rw [hb.sp, h.sp]⟩

/-- What is known after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  x22 : s.gpr .x22 = Dp s₀ + BitVec.ofNat 64 (16 * k)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (N s₀ - k)
  sp : s.sp = s₀.sp

theorem body_ct (v : Ctr32Impl) {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀')
    (hq : updateAArch64.pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ LInv s₀ k s₁ ∧ LInv s₀' k s₂) (body v.callee) fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x24])
      (.block (chainIn ++ updArgs)) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x22, .x23]) (.block advance) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun s₁ s₂ => k < N s₀ ∧ LInv s₀ k s₁ ∧ LInv s₀' k s₂) _
    (fun _ _ h => LInv.agree hq h.2.1 h.2.2) hA).wp
    (F₁ := Mid s₀ k) (F₂ := Mid s₀' k) fun _ _ h =>
      ⟨bodyMid_wp hp h.1 h.2.1, bodyMid_wp hp' (by rw [← pub_N hq]; exact h.1) h.2.2⟩
  have c := (ctr_rel v (P := fun s₁ s₂ => Mid s₀ k s₁ ∧ Mid s₀' k s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [pub_W hq, pub_S hq, pub_St hq, pub_R hq]; exact h.2.pre,
        by rw [h.1.sp, h.2.sp, pub_sp hq]⟩).wp
    (F₁ := After s₀ k) (F₂ := After s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (ctr_call v h.1.pre) fun _ hc =>
        ⟨by rw [hc.saved .x22 (by simp [preserved]) (by decide), h.1.x22],
          by rw [hc.saved .x23 (by simp [preserved]) (by decide), h.1.x23], by rw [hc.sp, h.1.sp]⟩,
       WP.mono (ctr_call v h.2.pre) fun _ hc =>
        ⟨by rw [hc.saved .x22 (by simp [preserved]) (by decide), h.2.x22],
          by rw [hc.saved .x23 (by simp [preserved]) (by decide), h.2.x23], by rw [hc.sp, h.2.sp]⟩⟩
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂) _
    (fun s₁ s₂ h => agree_of (by rw [h.1.sp, h.2.sp, pub_sp hq]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.x22, h.2.x22, pub_Dp hq]
      · rw [h.1.x23, h.2.x23, pub_N hq]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ LInv s₀ k s₁ ∧ LInv s₀' k s₂

theorem loop_ct (v : Ctr32Impl) {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀')
    (hq : updateAArch64.pub s₀ s₀') (n : Nat) :
    RelCT isa (LRel s₀ s₀' n) (.loop (body v.callee) (.nonzero .x .x23))
      fun s₁ s₂ => LInv s₀ (N s₀) s₁ ∧ LInv s₀' (N s₀') s₂ := by
  refine RelCT.loop (M := isa) (LRel s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have ct := (body_ct v hp hp' hq k).wp
    (F₁ := LInv s₀ (k + 1)) (F₂ := LInv s₀' (k + 1))
    fun _ _ h => ⟨body_ok v hp h.1 h.2.1, body_ok v hp' (by rw [← hN]; exact h.1) h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, l₁, l₂⟩ => ?_
  have hb : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  have e₁ := eval_x23 (x := N s₀ - (k + 1)) (by omega_using [hb]) l₁.x23
  have e₂ := eval_x23 (x := N s₀ - (k + 1)) (by omega_using [hb]) (by rw [l₂.x23, ← hN])
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : N s₀ = k + 1 := by
      have : N s₀ - (k + 1) = 0 := by simpa using hf
      omega_using [hk, this]
    exact ⟨h0 ▸ l₁, by rw [← hN, h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N s₀ - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [h0], l₁, l₂⟩

/-! ## The whole function -/

theorem update_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : updateAArch64.pre s₀)
    (h0' : updateAArch64.pre s₀') (hq : updateAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (update v.callee) fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  have hN := pub_N hq
  have hb : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  obtain ⟨_, hpro⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
      (.block (save ++ setup)) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hepi⟩ : ∃ h, (taint.check (Taint.ofRegs [.x24]) (.block restore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hnil⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have pro := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hq
      refine agree_of h7 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hpro).wp
    (F₁ := LInv s₀ 0) (F₂ := LInv s₀' 0)
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨prologue_wp hp, prologue_wp hp'⟩
  have ev {k : Nat} {s : State} (h : LInv s₀ 0 s) :
      isa.eval (.zero .x .x23) s = some (decide (N s₀ = 0)) :=
    eval_zero_x23 hb (by rw [h.x23]; rfl)
  have ev' {s : State} (h : LInv s₀' 0 s) : isa.eval (.zero .x .x23) s = some (decide (N s₀ = 0)) :=
    eval_zero_x23 hb (by rw [h.x23, ← hN]; rfl)
  have nil := RelCT.taint (A := taint)
    (P := fun a b => (LInv s₀ 0 a ∧ LInv s₀' 0 b) ∧ isa.eval (.zero .x .x23) a = some true) _
    (fun a b h => agree_of (by rw [h.1.1.sp, h.1.2.sp, pub_sp hq]) fun r hr => by simp at hr) hnil
  have mid : RelCT isa (fun a b => LInv s₀ 0 a ∧ LInv s₀' 0 b)
      (.ite (.zero .x .x23) (.block []) (.loop (body v.callee) (.nonzero .x .x23)))
      (fun a b => LInv s₀ (N s₀) a ∧ LInv s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev (k := 0) h.1, ev' h.2]) ?_ ?_
    · refine (nil.wp (F₁ := LInv s₀ (N s₀)) (F₂ := LInv s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; rw [ev (k := 0) h.1.1] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2)⟩
    · refine (loop_ct v hp hp' hq (N s₀ - 0)).mono (fun a b h => ⟨0, rfl, ?_, h.1.1, h.1.2⟩)
        fun _ _ h => h
      have := h.2; rw [ev (k := 0) h.1.1] at this
      have : N s₀ ≠ 0 := by simpa using this
      omega_using [this]
  have epi := RelCT.taint (A := taint) (P := fun a b => LInv s₀ (N s₀) a ∧ LInv s₀' (N s₀') b) _
    (fun a b h => agree_of (by rw [h.1.sp, h.2.sp, pub_sp hq]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.x24, h.2.x24, pub_S hq]) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h.2).seq (mid.seq epi)

theorem update_ct (v : Ctr32Impl) :
    ConstantTime isa updateAArch64.pre updateAArch64.pub (update v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (update_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.AArch64

end

end

/-! ### `CmacAes.AArch64.FinalizeCorrect`, which this module and modules that import it used -/

section

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_finalize` is correct

Before the call, the counter block (at `S + 2048`) holds `Mₙ ⊕ C`, for the
last block `Mₙ` of §6.2 step 4 and the chaining value `C` at `state`, the
state is zeroed, and `x19` and `x30` are saved in the scratch buffer; the call
leaves `CIPH_K(C ⊕ Mₙ)` there, the MAC (`macFull_split`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- The precondition, by name: the key (schedule and subkeys) `W`, the state
`St`, the last bytes `P` (`L` of them), the scratch buffer `S` and the
rounds `R`. -/
structure FPre (s₀ : State) (W St P S : Addr) (L R : Nat) : Prop where
  x0 : s₀.gpr .x0 = W
  x2 : s₀.gpr .x2 = St
  x3 : s₀.gpr .x3 = P
  x4 : (s₀.gpr .x4).toNat = L
  x5 : s₀.gpr .x5 = S
  x1 : (s₀.gpr .x1).toNat = R
  rd : s₀.rd = [⟨W, 272⟩, ⟨P, L⟩]
  wr : s₀.wr = [⟨St, 16⟩, ⟨S, 2176⟩]
  key_st : (⟨W, 272⟩ : Region).Disjoint ⟨St, 16⟩
  key_scr : (⟨W, 272⟩ : Region).Disjoint ⟨S, 2176⟩
  last_st : (⟨P, L⟩ : Region).Disjoint ⟨St, 16⟩
  last_scr : (⟨P, L⟩ : Region).Disjoint ⟨S, 2176⟩
  st_scr : (⟨St, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  key_wrap : W.toNat + 272 ≤ 2 ^ 64
  st_wrap : St.toNat + 16 ≤ 2 ^ 64
  last_wrap : P.toNat + L ≤ 2 ^ 64
  scr_wrap : S.toNat + 2176 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  len : L ≤ 16

theorem FPre.of {s₀ : State} (h : finalizeAArch64.pre s₀) :
    FPre s₀ (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat (s₀.gpr .x1).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes in `m`. -/
abbrev mn (m : Mem) (W P : Addr) (L : Nat) : List Byte :=
  Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 240) 16)
    (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 256) 16) (Spec.Aes.bytesAt m P L)

/-- What the branch on the length leaves: `Mₙ` in the counter block. -/
structure BPost (s₀ : State) (W St P S : Addr) (L : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = W
  x2 : s.gpr .x2 = St
  x5 : s.gpr .x5 = S
  x1 : s.gpr .x1 = s₀.gpr .x1
  saved : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨S + BitVec.ofNat 64 2048, 16⟩] s₀.mem s.mem
  blk : Spec.Aes.bytesAt s.mem (S + BitVec.ofNat 64 2048) 16 = mn s₀.mem W P L

section
variable {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R)
include hp

theorem FPre.inScr {d n : Nat} (h : d + n ≤ 2176) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := ⟨S, 2176⟩) (by simp) (Offset.contains_base _ h (by have := hp.scr_wrap; omega_arith))

theorem FPre.inKey {d n : Nat} (h : d + n ≤ 272) : InRegions (s₀.rd ++ s₀.wr) (W + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := ⟨W, 272⟩) (by simp) (Offset.contains_base _ h (by have := hp.key_wrap; omega_arith))

theorem FPre.inLast {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (P + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := ⟨P, L⟩) (by simp) (Offset.contains_base _ h (by have := hp.len; omega_arith))

end

theorem FPre.scrD {S : Addr} {d n : Nat} (h : d + n ≤ 2176) : Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 2176⟩ :=
  Offset.sub_base _ h

theorem wr_in {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem not_x9 {r : Reg} (hr : r ∈ preserved) : r ≠ .x9 := by rintro rfl; simp [preserved] at hr
theorem not_x10 {r : Reg} (hr : r ∈ preserved) : r ≠ .x10 := by rintro rfl; simp [preserved] at hr
theorem not_x6 {r : Reg} (hr : r ∈ preserved) : r ≠ .x6 := by rintro rfl; simp [preserved] at hr
theorem not_x7 {r : Reg} (hr : r ∈ preserved) : r ≠ .x7 := by rintro rfl; simp [preserved] at hr
theorem not_x8 {r : Reg} (hr : r ∈ preserved) : r ≠ .x8 := by rintro rfl; simp [preserved] at hr

theorem full_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) (hL : L = 16)
    {s : State} (hg : ∀ r, r ≠ .x9 → s.gpr r = s₀.gpr r) (hm : s.mem = s₀.mem) (hsp : s.sp = s₀.sp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block full) s (BPost s₀ W St P S L) := by
  subst hL
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  obtain ⟨s', run, mem, g, sp, rd, wr⟩ := xor2_ok s .x3 .x0 .x5 0 240 2048
    (P := P) (Q := W + BitVec.ofNat 64 240) (C := S + BitVec.ofNat 64 2048)
    (by decide) (by decide) (by decide)
    (by rw [hg _ (by decide), hp.x3, k0]) (by rw [hg _ (by decide), hp.x3])
    (by rw [hg _ (by decide), hp.x0]) (by rw [hg _ (by decide), hp.x0, Offset.add_add])
    (by rw [hg _ (by decide), hp.x5]) (by rw [hg _ (by decide), hp.x5, Offset.add_add])
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by rw [hrd, hwr]; simpa using hp.inLast (d := 0) (n := 8) (by decide))
    (by rw [hrd, hwr]; exact hp.inLast (d := 8) (n := 8) (by decide))
    (by rw [hrd, hwr]; exact hp.inKey (d := 240) (n := 8) (by decide))
    (by rw [hrd, hwr, Offset.add_add]; exact hp.inKey (d := 248) (n := 8) (by decide))
    (by rw [hwr]; exact hp.inScr (d := 2048) (n := 8) (by decide))
    (by rw [hwr, Offset.add_add]; exact hp.inScr (d := 2056) (n := 8) (by decide))
  rw [full_eq]
  refine WP.of_runBlock ⟨s', run, ?_⟩
  have gg (r : Reg) (h₁ : r ≠ .x9) (h₂ : r ≠ .x10) : s'.gpr r = s₀.gpr r := by rw [g r h₁ h₂, hg r h₁]
  refine ⟨by rw [gg _ (by decide) (by decide), hp.x0], by rw [gg _ (by decide) (by decide), hp.x2],
    by rw [gg _ (by decide) (by decide), hp.x5], gg _ (by decide) (by decide),
    fun r hr => gg r (not_x9 hr) (not_x10 hr), by rw [sp, hsp], by rw [rd, hrd],
    by rw [wr, hwr], by rw [mem, hm]; exact Proof.Cmac.xor2Mem_frame _ _ _ _, ?_⟩
  rw [mem, hm, Proof.Cmac.xor2Mem_bytes]
  · simp only [mn, Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length, ite_true]
    exact Proof.Cmac.xor_comm _ _
  · exact (hp.last_scr.symm.sub_left (FPre.scrD (d := 2048) (n := 8) (by decide))).sub_right
      (Offset.sub_base P (d := 8) (n := 8) (k := 16) (by decide))
  · rw [Offset.add_add]
    exact (hp.key_scr.symm.sub_left (FPre.scrD (d := 2048) (n := 8) (by decide))).sub_right
      (Offset.sub_base W (d := 248) (n := 8) (k := 272) (by decide))

open VG.WriteBytes in
theorem partial_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) (hL : L < 16)
    {s : State} (hg : ∀ r, r ≠ .x9 → s.gpr r = s₀.gpr r) (hm : s.mem = s₀.mem) (hsp : s.sp = s₀.sp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa partialBlock s (BPost s₀ W St P S L) := by
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  obtain hb : L < 2 ^ 64 := by omega_arith
  obtain h4 : s₀.gpr .x4 = BitVec.ofNat 64 L := by rw [← hp.x4]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨C, hC⟩ : ∃ C, S + BitVec.ofNat 64 2048 = C := ⟨_, rfl⟩
  obtain hc : s.gpr .x5 + BitVec.ofNat 64 2048 = C := by rw [hg _ (by decide), hp.x5, hC]
  obtain hc8 : s.gpr .x5 + BitVec.ofNat 64 2056 = C + BitVec.ofNat 64 8 := by
    rw [hg _ (by decide), hp.x5, ← hC, Offset.add_add]
  obtain dPC : (⟨P, L⟩ : Region).Disjoint ⟨C, 16⟩ := by rw [← hC]; exact hp.last_scr.sub_right (FPre.scrD (by decide))
  have dKC (d n : Nat) (h : d + n ≤ 272) : (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨C, 16⟩ := by
    rw [← hC]; exact (hp.key_scr.sub_left (Offset.sub_base _ h)).sub_right (FPre.scrD (by decide))
  -- Zero the block.
  obtain ⟨s₁, run₁, mem₁, x6₁, x7₁, x8₁, g₁, sp₁, rd₁, wr₁⟩ := zero_ok s hc hc8
    (by rw [hwr, ← hC]; exact hp.inScr (d := 2048) (n := 8) (by decide))
    (by rw [hwr, ← hC, Offset.add_add]; exact hp.inScr (d := 2056) (n := 8) (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain zf : s₁.mem = Proof.Cmac.zero2 s₀.mem C := by rw [mem₁, hm]
  obtain fz : Frame [⟨C, 16⟩] s₀.mem (Proof.Cmac.zero2 s₀.mem C) := Proof.Cmac.frame_store2 _ _ _
  obtain lastZ : Spec.Aes.bytesAt (Proof.Cmac.zero2 s₀.mem C) P L = Spec.Aes.bytesAt s₀.mem P L :=
    Proof.Cmac.bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dPC) (by omega_arith)
  have g₁' (r : Reg) (h₁ : r ≠ .x6) (h₂ : r ≠ .x7) (h₃ : r ≠ .x8) (h₄ : r ≠ .x9) : s₁.gpr r = s₀.gpr r := by
    rw [g₁ r h₁ h₂ h₃ h₄, hg r h₄]
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (s₂ : State) =>
      s₂.mem = writeBytes (Proof.Cmac.zero2 s₀.mem C) C (Spec.Aes.bytesAt s₀.mem P L) ∧
      s₂.gpr .x6 = C + BitVec.ofNat 64 L ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s₂.gpr r = s₀.gpr r) ∧
      s₂.sp = s₀.sp ∧ s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr) ?_ fun s₂ h₂ => ?_)
  · have ev : isa.eval (.zero .x .x4) s₁ = some (decide (L = 0)) := by
      show some (s₁.read .x .x4 == 0) = _
      rw [State.read, g₁' _ (by decide) (by decide) (by decide) (by decide), h4, BitVec.setWidth_eq]
      have := ofNat_ne_zero hb
      rw [bne] at this
      cases hx : (BitVec.ofNat 64 L == 0) <;> rw [hx] at this <;> cases hd : decide (L = 0) <;> simp_all
    by_cases hL0 : L = 0
    · subst hL0
      refine WP.ite true (by rw [ev]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [zf]; simp [Spec.Aes.bytesAt, writeBytes_nil], by rw [x6₁]; simp,
        fun r h₁ h₂ h₃ h₄ => g₁' r h₁ h₂ h₃ h₄, by rw [sp₁, hsp], by rw [rd₁, hrd], by rw [wr₁, hwr]⟩
    · refine WP.ite false (by rw [ev]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (copy_ok s₁ (P := P) (C := C) (by omega_arith) hL
        (by rw [x7₁, hg _ (by decide), hp.x3]) x6₁
        (by rw [x8₁, hg _ (by decide), h4])
        (fun i hi => by rw [rd₁, wr₁, hrd, hwr]; exact hp.inLast (d := i) (n := 1) (by omega_arith))
        (fun i hi => by
          rw [wr₁, hwr, ← hC, Offset.add_add]; exact hp.inScr (d := 2048 + i) (n := 1) (by omega_arith)) dPC) ?_
      rintro s₂ ⟨m₂, x6₂, g₂, sp₂, rd₂, wr₂⟩
      refine ⟨by rw [m₂, zf, lastZ], x6₂, fun r h₁ h₂ h₃ h₄ => by rw [g₂ r h₁ h₂ h₃ h₄, g₁' r h₁ h₂ h₃ h₄],
        by rw [sp₂, sp₁, hsp], by rw [rd₂, rd₁, hrd], by rw [wr₂, wr₁, hwr]⟩
  · obtain ⟨m₂, x6₂, g₂, sp₂, rd₂, wr₂⟩ := h₂
    rw [padK2_eq, WP.block_append_iff]
    obtain ⟨s₃, run₃, m₃, g₃, sp₃, rd₃, wr₃⟩ := pad_ok s₂ (B := C + BitVec.ofNat 64 L)
      (by rw [x6₂, BitVec.add_zero])
      (by rw [wr₂, ← hC, Offset.add_add]; exact hp.inScr (d := 2048 + L) (n := 1) (by omega_arith))
    refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
    obtain x5₃ : s₃.gpr .x5 = S := by
      rw [g₃ _ (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide), hp.x5]
    obtain x0₃ : s₃.gpr .x0 = W := by
      rw [g₃ _ (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide), hp.x0]
    obtain ⟨s₄, run₄, m₄, g₄, sp₄, rd₄, wr₄⟩ := xor2_ok s₃ .x5 .x0 .x5 2048 256 2048
      (P := C) (Q := W + BitVec.ofNat 64 256) (C := C) (by decide) (by decide) (by decide)
      (by rw [x5₃, hC]) (by rw [x5₃, ← hC, Offset.add_add]) (by rw [x0₃]) (by rw [x0₃, Offset.add_add])
      (by rw [x5₃, hC]) (by rw [x5₃, ← hC, Offset.add_add])
      ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
      (by rw [rd₃, wr₃, rd₂, wr₂, ← hC]; exact wr_in (hp.inScr (d := 2048) (n := 8) (by decide)))
      (by rw [rd₃, wr₃, rd₂, wr₂, ← hC, Offset.add_add]; exact wr_in (hp.inScr (d := 2056) (n := 8) (by decide)))
      (by rw [rd₃, wr₃, rd₂, wr₂]; exact hp.inKey (d := 256) (n := 8) (by decide))
      (by rw [rd₃, wr₃, rd₂, wr₂, Offset.add_add]; exact hp.inKey (d := 264) (n := 8) (by decide))
      (by rw [wr₃, wr₂, ← hC]; exact hp.inScr (d := 2048) (n := 8) (by decide))
      (by rw [wr₃, wr₂, ← hC, Offset.add_add]; exact hp.inScr (d := 2056) (n := 8) (by decide))
    refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
    have gg (r : Reg) (h₁ : r ≠ .x6) (h₂ : r ≠ .x7) (h₃ : r ≠ .x8) (h₄ : r ≠ .x9) (h₅ : r ≠ .x10) :
        s₄.gpr r = s₀.gpr r := by rw [g₄ r h₄ h₅, g₃ r h₄, g₂ r h₁ h₂ h₃ h₄]
    obtain hlen : (Spec.Aes.bytesAt s₀.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
    obtain fW : Frame [⟨C, 16⟩] (writeBytes (Proof.Cmac.zero2 s₀.mem C) C (Spec.Aes.bytesAt s₀.mem P L)) s₃.mem := by
      rw [m₃, m₂]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
    obtain fB : Frame [⟨C, 16⟩] (Proof.Cmac.zero2 s₀.mem C)
        (writeBytes (Proof.Cmac.zero2 s₀.mem C) C (Spec.Aes.bytesAt s₀.mem P L)) :=
      writeBytes_frame _ _ _ (by
        rw [hlen]; simpa using Offset.contains_base C (d := 0) (n := L) (k := 16) (by omega_arith) (by decide))
    obtain f₃ : Frame [⟨C, 16⟩] s₀.mem s₃.mem := (fz.trans fB).trans fW
    obtain k2 : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 256) 16 =
        Spec.Aes.bytesAt s₀.mem (W + BitVec.ofNat 64 256) 16 :=
      Proof.Cmac.bytesAt_frame16 f₃ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dKC 256 16 (by decide)
    obtain pad : Spec.Aes.bytesAt s₃.mem C 16 =
        Spec.Aes.bytesAt s₀.mem P L ++ [0x80] ++ Spec.Cmac.zeros (16 - L - 1) := by
      have := Proof.Cmac.padded_bytes (Proof.Cmac.zero2 s₀.mem C) C (Spec.Aes.bytesAt s₀.mem P L)
        (by rw [hlen]; exact hL) (Proof.Cmac.zero2_bytes _ _)
      rw [hlen] at this
      rw [m₃, m₂]; exact this
    refine ⟨by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), hp.x0],
      by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), hp.x2],
      by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), hp.x5],
      gg _ (by decide) (by decide) (by decide) (by decide) (by decide),
      fun r hr => gg r (not_x6 hr) (not_x7 hr) (not_x8 hr) (not_x9 hr) (not_x10 hr),
      by rw [sp₄, sp₃, sp₂], by rw [rd₄, rd₃, rd₂], by rw [wr₄, wr₃, wr₂], ?_, ?_⟩
    · rw [m₄, hC]; exact f₃.trans (Proof.Cmac.xor2Mem_frame _ _ _ _)
    · rw [m₄, hC, Proof.Cmac.xor2Mem_bytes, pad, k2]
      · simp only [mn, Spec.Cmac.lastBlock, hlen, show L ≠ 16 by omega_arith, ite_false]
        exact Proof.Cmac.xor_comm _ _
      · simpa using Offset.disjoint C (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by decide)
      · rw [Offset.add_add]
        exact (dKC 264 8 (by decide)).symm.sub_left (Region.sub_prefix (by decide))

/-! ## Up to the call -/

/-- What the code before the call leaves. -/
structure FMid (s₀ : State) (W St P S : Addr) (L R : Nat) (s : State) : Prop where
  pre : CallPre s W (S + BitVec.ofNat 64 2048) St S R
  blk : Spec.Aes.bytesAt s.mem (S + BitVec.ofNat 64 2048) 16 =
    Spec.Cmac.xor (mn s₀.mem W P L) (Spec.Aes.bytesAt s₀.mem St 16)
  frame : Frame [⟨S + BitVec.ofNat 64 2048, 16⟩, ⟨St, 16⟩, ⟨S + BitVec.ofNat 64 2064, 16⟩] s₀.mem s.mem
  slot19 : s.mem.readW (S + BitVec.ofNat 64 2064) 64 = s₀.gpr .x19
  slot30 : s.mem.readW (S + BitVec.ofNat 64 2072) 64 = s₀.gpr .x30
  x19 : s.gpr .x19 = S
  saved : ∀ r ∈ preserved, r ≠ .x19 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finArgs_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) {s : State}
    (h : BPost s₀ W St P S L s) : WP isa (.block finArgs) s (FMid s₀ W St P S L R) := by
  have sw := hp.scr_wrap
  have tw := hp.st_wrap
  rw [finArgs_eq, WP.block_append_iff]
  obtain hRegs : s.rd ++ s.wr = [⟨W, 272⟩, ⟨P, L⟩, ⟨St, 16⟩, ⟨S, 2176⟩] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have inC (d : Nat) (hd : d + 8 ≤ 2176) : InRegions s.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [h.wr]; exact hp.inScr (by omega_arith)
  have inSt (d : Nat) (hd : d + 8 ≤ 16) : InRegions s.wr (St + BitVec.ofNat 64 d) 8 := by
    rw [h.wr, hp.wr]; exact in_rw (r := ⟨St, 16⟩) (by simp) (Offset.contains_base _ hd (by omega_arith))
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := xor2_ok s .x5 .x2 .x5 2048 0 2048
    (P := S + BitVec.ofNat 64 2048) (Q := St) (C := S + BitVec.ofNat 64 2048) (by decide) (by decide) (by decide)
    (by rw [h.x5]) (by rw [h.x5, Offset.add_add]) (by rw [h.x2, k0]) (by rw [h.x2])
    (by rw [h.x5]) (by rw [h.x5, Offset.add_add]) ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (wr_in (inC 2048 (by decide))) (by rw [Offset.add_add]; exact wr_in (inC 2056 (by decide)))
    (by simpa using wr_in (inSt 0 (by decide))) (wr_in (inSt 8 (by decide)))
    (inC 2048 (by decide)) (by rw [Offset.add_add]; exact inC 2056 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, m₂, x3₂, x2₂, x4₂, x19₂, g₂, sp₂, rd₂, wr₂⟩ := args_ok s₁ (D := St) (S := S)
    (by rw [g₁ _ (by decide) (by decide), h.x2]) (by rw [g₁ _ (by decide) (by decide), h.x5])
    (by rw [wr₁]; exact inSt 0 (by decide)) (by rw [wr₁]; exact inSt 8 (by decide))
    (by rw [wr₁]; exact inC 2064 (by decide)) (by rw [wr₁]; exact inC 2072 (by decide))
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have g (r : Reg) (h₁ : r ≠ .x2) (h₂ : r ≠ .x3) (h₃ : r ≠ .x4) (h₄ : r ≠ .x9) (h₅ : r ≠ .x19) (h₆ : r ≠ .x10) :
      s₂.gpr r = s.gpr r := by
    rw [g₂ r h₁ h₂ h₃ h₄ h₅, g₁ r h₄ h₆]
  obtain dCSt : (⟨S + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint ⟨St, 16⟩ :=
    hp.st_scr.symm.sub_left (FPre.scrD (by decide))
  obtain dSlSt : (⟨S + BitVec.ofNat 64 2064, 16⟩ : Region).Disjoint ⟨St, 16⟩ :=
    hp.st_scr.symm.sub_left (FPre.scrD (by decide))
  obtain dSlC : (⟨S + BitVec.ofNat 64 2064, 16⟩ : Region).Disjoint ⟨S + BitVec.ofNat 64 2048, 16⟩ :=
    Offset.disjoint S (by decide) (by omega_arith) (by omega_arith)
  -- The memory: the state zeroed, then the two slots.
  obtain ⟨Z, hZ⟩ : ∃ Z, (s₁.mem.writeW (St + BitVec.ofNat 64 0) (0 : BitVec 64)).writeW (St + BitVec.ofNat 64 8)
      (0 : BitVec 64) = Z := ⟨_, rfl⟩
  obtain e72 : S + BitVec.ofNat 64 2072 = S + BitVec.ofNat 64 2064 + BitVec.ofNat 64 8 :=
    (Offset.add_add_eq S (a := 2064) (b := 8) (c := 2072) rfl).symm
  obtain fSl : Frame [⟨S + BitVec.ofNat 64 2064, 16⟩] Z s₂.mem := by
    rw [m₂, hZ, e72]; exact Proof.Cmac.frame_store2 _ _ _
  obtain fZ : Frame [⟨St, 16⟩] s₁.mem Z := by rw [← hZ]; exact frame_store2' _ _ _
  obtain stS : Spec.Aes.bytesAt s.mem St 16 = Spec.Aes.bytesAt s₀.mem St 16 :=
    Proof.Cmac.bytesAt_frame16 h.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dCSt.symm
  have hR := hp.rounds
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [rd₂, rd₁, h.rd], by rw [wr₂, wr₁, h.wr]⟩
  · exact
    { x0 := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x0]
      x1 := by
        rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x1]
        apply BitVec.eq_of_toNat_eq; simp [hp.x1]; omega_arith
      x2 := x2₂
      x3 := x3₂
      x4 := x4₂
      x5 := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x5]
      rounds := hR
      wc := (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right (FPre.scrD (by decide))
      wd := hp.key_st.sub_left (Region.sub_prefix (by decide))
      ws := (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      cd := dCSt
      cs := Offset.disjoint_base _ (by decide) (by omega_arith)
      ds := hp.st_scr.sub_right (Region.sub_prefix (by decide))
      wrap := hp.st_wrap
      reads := by
        rw [rd₂, wr₂, rd₁, wr₁, hRegs]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨⟨W, 272⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨S, 2176⟩, by simp, 2048, rfl, by simp⟩
        · exact ⟨⟨St, 16⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₂, wr₁, h.wr, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨S, 2176⟩, by simp, 2048, rfl, by simp⟩
        · exact ⟨⟨St, 16⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
      zero := by
        rw [Proof.Cmac.bytesAt_frame16 fSl (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact dSlSt.symm), ← hZ, k0,
          Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero, Proof.Cmac.zeros_8_8] }
  · rw [Proof.Cmac.bytesAt_frame16 fSl (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dSlC.symm),
      Proof.Cmac.bytesAt_frame16 fZ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dCSt),
      m₁, Proof.Cmac.xor2Mem_bytes, h.blk, stS]
    · simpa using Offset.disjoint (S + BitVec.ofNat 64 2048) (d := 0) (n := 8) (e := 8) (k := 8) (by decide)
        (by decide) (by decide)
    · exact (dCSt.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  · refine (((h.frame.trans (m₁ ▸ Proof.Cmac.xor2Mem_frame _ _ _ _)).mono (by simp)).trans
      (fZ.mono (by simp))).trans (fSl.mono (by simp))
  · rw [m₂, readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64,
      g₁ _ (by decide) (by decide), h.saved _ (by simp [preserved])]
  · rw [m₂, Mem.readW_writeW_self64, g₁ _ (by decide) (by decide), h.saved _ (by simp [preserved])]
  · exact x19₂
  · intro r hr h19
    obtain n2 : r ≠ .x2 := by rintro rfl; simp [preserved] at hr
    obtain n3 : r ≠ .x3 := by rintro rfl; simp [preserved] at hr
    obtain n4 : r ≠ .x4 := by rintro rfl; simp [preserved] at hr
    rw [g r n2 n3 n4 (not_x9 hr) h19 (not_x10 hr), h.saved r hr]
  · rw [sp₂, sp₁, h.sp]

theorem finPre_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) :
    WP isa finPre s₀ (FMid s₀ W St P S L R) := by
  obtain h4 : s₀.gpr .x4 = BitVec.ofNat 64 L := by rw [← hp.x4]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨s₁, run₁, ev₁, g₁, sp₁, m₁, rd₁, wr₁⟩ := sub16_ok s₀ h4 hp.len
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Q := BPost s₀ W St P S L) ?_ fun _ h => finArgs_wp hp h)
  by_cases hL : L = 16
  · exact WP.ite true (by rw [ev₁]; simp [hL]) (fun _ => full_wp hp hL g₁ m₁ sp₁ rd₁ wr₁)
      (fun h => by cases h)
  · exact WP.ite false (by rw [ev₁]; simp [hL]) (fun h => by cases h)
      (fun _ => partial_wp hp (by have := hp.len; omega_arith) g₁ m₁ sp₁ rd₁ wr₁)

theorem restoreF_ok (s : State) {B : Addr} (hb : s.gpr .x19 = B)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 2072) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 2064) 8) :
    ∃ s', runBlock isa [.ldr .x .x30 .x19 2072, .ldr .x .x19 .x19 2064] s = some s' ∧
      s'.gpr .x30 = s.mem.readW (B + BitVec.ofNat 64 2072) 64 ∧
      s'.gpr .x19 = s.mem.readW (B + BitVec.ofNat 64 2064) 64 ∧
      (∀ r, r ≠ .x19 → r ≠ .x30 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
      State.load, Size.bytes, Size.bits, gpr_write, mem_write, rd_write, wr_write, 
      Option.bind_some, Option.map_some, hb, r₁, r₂]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write, Mem.readW], by simp [gpr_write, Mem.readW],
    fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, rfl⟩

theorem finalize_wp (v : Ctr32Impl) {s₀ : State} (h0 : finalizeAArch64.pre s₀) :
    WP isa (finalize v.callee) s₀ fun s' => GprAbi s₀ s' ∧ finalizeAArch64.post s₀ s' := by
  obtain hp := FPre.of h0
  generalize s₀.gpr .x0 = W at hp
  generalize s₀.gpr .x2 = St at hp
  generalize s₀.gpr .x3 = P at hp
  generalize s₀.gpr .x5 = S at hp
  generalize (s₀.gpr .x4).toNat = L at hp
  generalize (s₀.gpr .x1).toNat = R at hp
  have hR := hp.rounds
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> omega_arith
  have sw := hp.scr_wrap
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ctr_call v h₁.pre) fun s₂ h₂ => ?_)
  obtain x19₂ : s₂.gpr .x19 = S := by rw [h₂.saved .x19 (by simp [preserved]) (by decide), h₁.x19]
  obtain rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]
  obtain ⟨s₃, run₃, x30₃, x19₃, g₃, sp₃, mem₃⟩ := restoreF_ok s₂ x19₂
    (by rw [rdwr₂]; exact wr_in (hp.inScr (d := 2072) (n := 8) (by decide)))
    (by rw [rdwr₂]; exact wr_in (hp.inScr (d := 2064) (n := 8) (by decide)))
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  -- The slots, which the call does not write.
  have slots (d : Nat) (h₁' : 2064 ≤ d) (h₂' : d + 8 ≤ 2080) :
      s₂.mem.readW (S + BitVec.ofNat 64 d) 64 = s₁.mem.readW (S + BitVec.ofNat 64 d) 64 := by
    refine h₂.frame.readW (r := ⟨S + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint S (by omega_arith) (by omega_arith) (by omega_arith)
    · exact (hp.st_scr.symm.sub_left (FPre.scrD (by omega_arith)))
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  obtain big : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s₀.mem s₂.mem := by
    refine (h₁.frame.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨S, 2176⟩, by simp, FPre.scrD (by decide)⟩
      · exact ⟨⟨St, 16⟩, by simp, fun _ h => h⟩
      · exact ⟨⟨S, 2176⟩, by simp, FPre.scrD (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨S, 2176⟩, by simp, FPre.scrD (by decide)⟩
      · exact ⟨⟨St, 16⟩, by simp, fun _ h => h⟩
      · exact ⟨⟨S, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
  obtain sch : Spec.Aes.bytesAt s₁.mem W (16 * (R + 1)) = Spec.Aes.bytesAt s₀.mem W (16 * (R + 1)) :=
    Proof.Cmac.bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hp.key_scr.sub_left (Region.sub_prefix (by omega_arith))).sub_right (FPre.scrD (by decide))
      · exact hp.key_st.sub_left (Region.sub_prefix (by omega_arith))
      · exact (hp.key_scr.sub_left (Region.sub_prefix (by omega_arith))).sub_right (FPre.scrD (by decide))) (by omega_arith)
  refine ⟨⟨fun r hr => ?_, by rw [sp₃, h₂.sp, h₁.sp]⟩, ?_⟩
  · by_cases h19 : r = .x19
    · subst h19; rw [x19₃, slots 2064 (by decide) (by decide), h₁.slot19]
    by_cases h30 : r = .x30
    · subst h30; rw [x30₃, slots 2072 (by decide) (by decide), h₁.slot30]
    rw [g₃ r h19 h30, h₂.saved r hr h30, h₁.saved r hr h19]
  · intro hk msg hm hne hst
    rw [hp.x0, hp.x1] at hk hst ⊢
    rw [hp.x2] at hst ⊢
    rw [hp.x4] at hne
    rw [hp.x3, hp.x4]
    obtain ⟨e1, e2⟩ := Proof.Cmac.k1k2 (Proof.Cmac.subkeys_aes_length _ _) hk
    rw [mem₃, h₂.out, sch, h₁.blk, mn, e1, e2, hst,
      Proof.Cmac.macFull_split _ hm (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
        (by rw [Proof.Cmac.bytesAt_length]; exact hne), Proof.Cmac.xor_comm]

end VG.Proof.CmacAes.AArch64

end

end

@[expose] public section

section

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_subkeys` is constant time

The code before the call and after it is checked by the taint analysis, from
the registers the correctness proof pins (the arguments, then `x19` and
`x20`); the call of `vg_aes_ctr32` is constant time by its own proof
(`ctr_rel`).
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- What is known between the code before the call and the call. -/
structure SMid (s₀ : State) (W K S : Addr) (R : Nat) (s : State) : Prop where
  pre : CallPre s W (S + BitVec.ofNat 64 2048) K S R
  x19 : s.gpr .x19 = K
  x20 : s.gpr .x20 = S
  sp : s.sp = s₀.sp

theorem smid_wp {s₀ : State} {W K S : Addr} {R : Nat} (hp : SPre s₀ W K S R) :
    WP isa (.block subkeysPre) s₀ (SMid s₀ W K S R) := by
  have sw := hp.scr_wrap
  have kw := hp.k_wrap
  have inS (d : Nat) (h : d + 8 ≤ 2176) : InRegions s₀.wr (s₀.gpr .x3 + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr, hp.x3]; exact in_rw (r := ⟨S, 2176⟩) (by simp) (Offset.contains_base _ h (by omega_using [h]))
  have inK (d : Nat) (h : d + 8 ≤ 32) : InRegions s₀.wr (s₀.gpr .x2 + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr, hp.x2]; exact in_rw (r := ⟨K, 32⟩) (by simp) (Offset.contains_base _ h (by omega_using [h]))
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x4₁, x5₁, x19₁, x20₁, _, sp₁, mem₁, rd₁, wr₁⟩ :=
    subkeysPre_ok s₀ (inS _ (by decide)) (inS _ (by decide)) (inS _ (by decide)) (inS _ (by decide))
      (inS _ (by decide)) (inK _ (by decide)) (inK _ (by decide))
  exact WP.of_runBlock ⟨s₁, run₁,
    callPre_of hp x0₁ x1₁ x2₁ x3₁ x4₁ x5₁ mem₁ rd₁ wr₁, by rw [x19₁, hp.x2], by rw [x20₁, hp.x3], sp₁⟩

theorem subkeys_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : subkeysAArch64.pre s₀)
    (h0' : subkeysAArch64.pre s₀') (hq : subkeysAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (subkeys v.callee) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp := SPre.of h0
  have hp' : SPre s₀' (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x1).toNat := by
    rw [q1, q2, q3, q4]; exact SPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3]) (.block subkeysPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20]) (.block subkeysPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine agree_of q5 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := SMid s₀ _ _ _ _) (F₂ := SMid s₀' _ _ _ _) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨smid_wp hp, smid_wp hp'⟩
  have c := (ctr_rel v (P := fun s₁ s₂ =>
      SMid s₀ (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x1).toNat s₁ ∧
      SMid s₀' (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x1).toNat s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, h.2.pre, by rw [h.1.sp, h.2.sp, q5]⟩).wp
    (F₁ := fun (s : State) => s.gpr .x19 = s₀.gpr .x2 ∧ s.gpr .x20 = s₀.gpr .x3 ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .x19 = s₀.gpr .x2 ∧ s.gpr .x20 = s₀.gpr .x3 ∧ s.sp = s₀'.sp)
    fun s₁ s₂ h =>
      ⟨WP.mono (ctr_call v h.1.pre) fun _ hc =>
        ⟨by rw [hc.saved .x19 (by simp [preserved]) (by decide), h.1.x19],
          by rw [hc.saved .x20 (by simp [preserved]) (by decide), h.1.x20], by rw [hc.sp, h.1.sp]⟩,
       WP.mono (ctr_call v h.2.pre) fun _ hc =>
        ⟨by rw [hc.saved .x19 (by simp [preserved]) (by decide), h.2.x19],
          by rw [hc.saved .x20 (by simp [preserved]) (by decide), h.2.x20], by rw [hc.sp, h.2.sp]⟩⟩
  have b := RelCT.taint (A := taint)
    (P := fun s₁ s₂ => (s₁.gpr .x19 = s₀.gpr .x2 ∧ s₁.gpr .x20 = s₀.gpr .x3 ∧ s₁.sp = s₀.sp) ∧
      (s₂.gpr .x19 = s₀.gpr .x2 ∧ s₂.gpr .x20 = s₀.gpr .x3 ∧ s₂.sp = s₀'.sp)) _
    (fun s₁ s₂ h => agree_of (by rw [h.1.2.2, h.2.2.2, q5]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2.1, h.2.2.1]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem subkeys_ct (v : Ctr32Impl) :
    ConstantTime isa subkeysAArch64.pre subkeysAArch64.pub (subkeys v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (subkeys_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.AArch64

end

section

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_finalize` is constant time

The code before the call is checked by the taint analysis (its branches and
the copy loop depend only on `last_len`), the call of `vg_aes_ctr32` is
constant time by its own proof (`ctr_rel`), its arguments pinned by the
correctness proof (`FMid`), and the restore after it by the taint analysis
again, from `x19` (the scratch buffer).
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

theorem finalize_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : finalizeAArch64.pre s₀)
    (h0' : finalizeAArch64.pre s₀') (hq : finalizeAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finalize v.callee) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have hp := FPre.of h0
  have hp' : FPre s₀' (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat
      (s₀.gpr .x1).toNat := by
    rw [q1, q2, q3, q4, q5, q6]; exact FPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) finPre h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19])
      (.block [.ldr .x .x30 .x19 2072, .ldr .x .x19 .x19 2064]) h).isSome = true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine agree_of q7 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := FMid s₀ _ _ _ _ _ _) (F₂ := FMid s₀' _ _ _ _ _ _) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨finPre_wp hp, finPre_wp hp'⟩
  have c := (ctr_rel v (P := fun s₁ s₂ =>
      FMid s₀ (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat (s₀.gpr .x1).toNat s₁ ∧
      FMid s₀' (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat (s₀.gpr .x1).toNat s₂)
    fun s₁ s₂ h => ⟨h.1.pre, h.2.pre, by rw [h.1.sp, h.2.sp, q7]⟩).wp
    (F₁ := fun (s : State) => s.gpr .x19 = s₀.gpr .x5 ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .x19 = s₀.gpr .x5 ∧ s.sp = s₀'.sp) fun s₁ s₂ h =>
      ⟨WP.mono (ctr_call v h.1.pre) fun _ hc =>
        ⟨by rw [hc.saved .x19 (by simp [preserved]) (by decide), h.1.x19], by rw [hc.sp, h.1.sp]⟩,
       WP.mono (ctr_call v h.2.pre) fun _ hc =>
        ⟨by rw [hc.saved .x19 (by simp [preserved]) (by decide), h.2.x19], by rw [hc.sp, h.2.sp]⟩⟩
  have b := RelCT.taint (A := taint)
    (P := fun s₁ s₂ => (s₁.gpr .x19 = s₀.gpr .x5 ∧ s₁.sp = s₀.sp) ∧ (s₂.gpr .x19 = s₀.gpr .x5 ∧ s₂.sp = s₀'.sp)) _
    (fun s₁ s₂ h => agree_of (by rw [h.1.2, h.2.2, q7]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.1, h.2.1]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem finalize_ct (v : Ctr32Impl) :
    ConstantTime isa finalizeAArch64.pre finalizeAArch64.pub (finalize v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finalize_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.AArch64

end

/-!
# AES-CMAC on AArch64: `Verified`

Correctness and constant time (for any implementation `v` of `vg_aes_ctr32`),
a state satisfying each precondition, and the shared contracts of
`Spec/Cmac/Contract.lean` (with no stack: the calls keep the return address in
`x30`, which each function saves in the scratch buffer).
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

theorem update_keepsV (v : Ctr32Impl) : (update v.callee).allInstrs keepsV = true := by
  simp only [update, body, Code.allInstrs, v.keepsV]; decide +kernel

theorem subkeys_keepsV (v : Ctr32Impl) : (subkeys v.callee).allInstrs keepsV = true := by
  simp only [subkeys, Code.allInstrs, v.keepsV]; decide +kernel

theorem finalize_keepsV (v : Ctr32Impl) : (finalize v.callee).allInstrs keepsV = true := by
  simp only [finalize, finPre, partialBlock, copy, Code.allInstrs, v.keepsV]; decide +kernel

theorem update_correct (v : Ctr32Impl) (s : State) (hs : updateAArch64.pre s) :
    ∃ t s', Exec isa (update v.callee) s t s' ∧ abiPreserved s s' ∧ updateAArch64.post s s' :=
  WP.withPreservedV (update_wp v hs) (update_keepsV v)

theorem subkeys_correct (v : Ctr32Impl) (s : State) (hs : subkeysAArch64.pre s) :
    ∃ t s', Exec isa (subkeys v.callee) s t s' ∧ abiPreserved s s' ∧ subkeysAArch64.post s s' :=
  WP.withPreservedV (subkeys_wp v hs) (subkeys_keepsV v)

theorem finalize_correct (v : Ctr32Impl) (s : State) (hs : finalizeAArch64.pre s) :
    ∃ t s', Exec isa (finalize v.callee) s t s' ∧ abiPreserved s s' ∧ finalizeAArch64.post s s' :=
  WP.withPreservedV (finalize_wp v hs) (finalize_keepsV v)

end VG.Proof.CmacAes.AArch64

end

end

/-! The register-resident CMAC loop, proven against the existing shared
contract. Memory is unchanged until the final chaining value is stored. -/

@[expose] public section

namespace VG.Proof.CmacAes.AArch64.Aese
open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Proof.Aes.AArch64.Aese
open VG.Impl.Aes.AArch64.Aese (kreg aes)
open VG.Impl.CmacAes.AArch64.Aese

abbrev schedule (s : State) := Spec.Aes.bytesAt s.mem (W s) (16 * (R s + 1))
def bytes (v : BitVec 128) : List Byte := (st v).toList

theorem bytes_read (m : Mem) (p : Addr) : bytes (m.readW p 128) = Spec.Aes.bytesAt m p 16 := by
  apply List.ext_getElem
  · simp [bytes, Spec.Aes.bytesAt]
  · intro i hi hj
    simpa [bytes, st, Spec.Aes.bytesAt] using vbyte_readW m p (i := i) (by simpa [bytes] using hi)

theorem bytes_xor (a b : BitVec 128) : bytes (a ^^^ b) = Spec.Cmac.xor (bytes a) (bytes b) := by
  apply List.ext_getElem
  · simp [bytes, Spec.Cmac.xor]
  · intro i hi hj
    simpa [bytes, st, Spec.Cmac.xor] using vbyte_xor a b i

theorem state_bytes (v : BitVec 128) : (Vector.ofFn fun i : Fin 16 => (bytes v).getD i 0) = st v := by
  apply st_ext
  intro i hi
  simp [bytes, Vector.getD, hi]

structure PlainInv (s₀ : State) (k : Nat) (s : State) : Prop where
  keys : Keys (R s₀) (schedule s₀) s
  x2 : s.gpr .x2 = St s₀
  x3 : s.gpr .x3 = Dp s₀ + BitVec.ofNat 64 (16 * k)
  x4 : s.gpr .x4 = BitVec.ofNat 64 (N s₀ - k)
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : bytes (s.v .v0) = Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem (St s₀) 16) ((blks s₀).take k)

theorem key_in {s₀ : State} (hp : UPre s₀) {o : Nat} (h : o + 16 ≤ 240) :
    InRegions (s₀.rd ++ s₀.wr) (W s₀ + BitVec.ofNat 64 o) 16 :=
  ⟨schR s₀, by rw [hp.rd]; simp, Offset.contains_base _ h (by omega_arith)⟩

theorem setupKeys_ok {s₀ : State} (hp : UPre s₀) : WP isa (.block setupKeys) s₀ (PlainInv s₀ 0) := by
  have hR := hp.rounds
  have hx1 := x1_ofNat s₀
  rw [setupKeys, WP.block_append_iff]
  refine WP.mono (loads_ok s₀ (fun j hj => key_in hp (by omega_arith)) 13 (Nat.le_refl _))
    fun s₁ ⟨e₁, f₁⟩ => ?_
  have g : ∀ r, s₁.gpr r = s₀.gpr r := fun r => f₁.gpr r (by simp)
  have e9 : s₁.gpr .x0 + s₁.gpr .x1 <<< 4 = W s₀ + BitVec.ofNat 64 (16 * R s₀) := by
    rw [g, g, VG.Proof.Aes.AArch64.shl4]
  have e9' : W s₀ + BitVec.ofNat 64 (16 * R s₀) - BitVec.ofNat 64 16 =
      W s₀ + BitVec.ofNat 64 (16 * (R s₀ - 1)) := by
    rw [Offset.add_ofNat_sub _ (by omega_arith), show 16 * R s₀ - 16 = 16 * (R s₀ - 1) by omega_arith]
  have rdwr : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [f₁.rd, f₁.wr]
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsl_x (sh := 4) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_add, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 0) (by decide) (by
    simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, e9,
      BitVec.add_zero, rdwr]
    exact key_in hp (by omega_arith)), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 0) (by decide) (by
    simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9, e9', BitVec.add_zero, rdwr]
    exact key_in hp (by omega_arith)), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 10) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 12) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 0) (by decide) (by
    simp only [State.setV, State.write, reduceCtorEq, ite_false, BitVec.add_zero, rdwr, g]
    exact ⟨stR s₀, by rw [hp.wr]; simp, Region.contains_self _ _⟩), WP.block_nil ?_⟩
  have hL : ∀ j, j ≤ R s₀ → 16 * j + 16 ≤ 16 * (R s₀ + 1) := fun j hj => by omega_arith
  refine ⟨⟨hR, fun j hj => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, f₁.rd, f₁.wr, ?_⟩
  · simp only [State.setV, State.write, (kreg_ne j).1, (kreg_ne j).2, ite_false,
      show kreg j ≠ .v0 by unfold kreg; split <;> decide]
    rw [e₁ j (by omega_arith)]
    exact keyIs_readW _ _ (hL j (by omega_arith))
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9, e9', BitVec.add_zero, f₁.mem]
    exact keyIs_readW _ _ (hL _ (by omega_arith))
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9, BitVec.add_zero, f₁.mem]
    exact keyIs_readW _ _ (hL _ (Nat.le_refl _))
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, g, hx1]; rfl
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, g, hx1]; rfl
  · simp [State.setV, State.write, g]
  · simp [State.setV, State.write, g]
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, g]
    exact x4_ofNat s₀
  · exact f₁.mem
  · simp only [State.setV, State.write, ite_true, reduceCtorEq, ite_false, g, BitVec.add_zero, f₁.mem]
    exact bytes_read _ _

structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  keys : Keys (R s₀) (schedule s₀) s
  combo : s.v .v31 = s.v .v16 ^^^ s.v .v30
  x2 : s.gpr .x2 = St s₀
  x3 : s.gpr .x3 = Dp s₀ + BitVec.ofNat 64 (16 * k)
  x4 : s.gpr .x4 = BitVec.ofNat 64 (N s₀ - k)
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : bytes (s.v .v0 ^^^ s.v .v30) = Spec.Cmac.chain (ciph s₀)
    (Spec.Aes.bytesAt s₀.mem (St s₀) 16) ((blks s₀).take k)

theorem vframe_setV {rs : List VReg} {s t : State} (h : VFrame rs s t) {d : VReg} (hd : d ∈ rs)
    (x : BitVec 128) : VFrame rs s (t.setV d x) :=
  ⟨h.gpr, h.sp, h.mem, h.rd, h.wr, fun r hr => by
    rw [v_setV_of_ne (h := fun e => hr (by rw [e]; exact hd)), h.v r hr]⟩

theorem setup_ok {s₀ : State} (hp : UPre s₀) : WP isa (.block setup) s₀ (Inv s₀ 0) := by
  rw [setup, WP.block_append_iff]
  refine WP.mono (setupKeys_ok hp) fun s h => ?_
  rw [fold, WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ?_⟩
  have vf : VFrame [.v0, .v31] s
      ((s.setV .v31 (s.v .v16 ^^^ s.v .v30)).setV .v0 (s.v .v0 ^^^ s.v .v30)) := by
    exact vframe_setV (vframe_setV (VFrame.refl _ s) (by decide) _) (by decide) _
  refine ⟨h.keys.of_frame vf ⟨by decide, by decide⟩, ?_, h.x2, h.x3, h.x4, h.mem, h.rd, h.wr, ?_⟩
  · simp [State.setV]
  · simpa [State.setV, BitVec.xor_assoc] using h.state

theorem exec_eor16 (s : State) (d n m : VReg) :
    exec (.vop (.logic .eor d n m)) s = some (s.setV d (s.v n ^^^ s.v m)) := rfl

theorem exec_aese (s : State) (d n : VReg) :
    exec (.vop (.aese d n)) s = some (s.setV d (aesMapBytes aesSbox (aesShiftRows (s.v d ^^^ s.v n)))) := rfl

theorem exec_aesmc (s : State) (d n : VReg) :
    exec (.vop (.aesmc d n)) s = some (s.setV d (aesMixColumns (s.v n))) := rfl

theorem folded_xor (a m k l : BitVec 128) :
    a ^^^ (m ^^^ (k ^^^ l)) = ((a ^^^ l) ^^^ m) ^^^ k := by
  ac_rfl

/-- The first full round: the input block, first round key and deferred
last round key are XORed before the chaining register is read. -/
theorem absorb_ok {nr : Nat} {w : List Byte} (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 0) 16)
    (hK : Keys nr w s) (hc : s.v .v31 = s.v .v16 ^^^ s.v .v30) :
    WP isa (.block absorb) s fun s' =>
      RInv [.v0] w (fun _ => st ((s.v .v0 ^^^ s.v .v30) ^^^ s.mem.readW (s.gpr .x3) 128)) 1 s' ∧
      VFrame [.v0, .v1] s s' := by
  rw [absorb, WP.block_cons_iff]
  refine ⟨_, exec_ldrq (by decide) hin, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_eor16 _ _ _ _, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_aese _ _ _, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_aesmc _ _ _, WP.block_nil ?_⟩
  refine ⟨?_, vframe_setV (vframe_setV (vframe_setV (vframe_setV (VFrame.refl _ s) (by decide) _)
    (by decide) _) (by decide) _) (by decide) _⟩
  intro b hb
  simp only [List.mem_singleton] at hb; subst hb
  simp only [State.setV, ite_true, reduceCtorEq, ite_false, BitVec.add_zero, hc]
  rw [folded_xor]
  exact round_st (hK.full 0 (by have := hK.rounds; omega_arith)) (rnds_zero w _).symm

theorem rounds_tail_ok {nr : Nat} {w : List Byte} {x : VReg → Spec.Aes.State} {s : State}
    (hK : Keys nr w s) (hI : RInv [.v0] w x 1 s) :
    ∀ k, k + 2 ≤ nr →
    WP isa (.block ((List.range k).flatMap fun j => VG.Impl.Aes.AArch64.Aese.rnd [.v0] (kreg (j + 1)))) s
      fun s' => RInv [.v0] w x (k + 1) s' ∧ VFrame [.v0] s s'
  | 0, _ => WP.block_nil ⟨hI, VFrame.refl _ _⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (rounds_tail_ok hK hI k (by omega_arith)) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have br : BlockRegs [.v0] := ⟨by decide, by decide⟩
    exact WP.mono (round_ok br (j := k + 1) (by omega_arith) (hK.of_frame hf₁ br) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩

theorem folded_last_ok {nr : Nat} {w : List Byte} {x : VReg → Spec.Aes.State} {s : State}
    (hK : Keys nr w s) (hI : RInv [.v0] w x (nr - 1) s) :
    WP isa (.block [.vop (.aese .v0 .v29)]) s fun s' =>
      st (s'.v .v0 ^^^ s'.v .v30) = Spec.Aes.cipher nr w (x .v0) ∧ VFrame [.v0] s s' := by
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ?_⟩
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩⟩
  · simp only [State.setV, ite_true, reduceCtorEq, ite_false]
    exact last_st hK.k29 hK.k30 (hI .v0 (by simp))
  · intro r hr; simp only [List.mem_singleton] at hr
    simp [State.setV, hr]

theorem tail_ok {nr middle : Nat} {w : List Byte} {x : VReg → Spec.Aes.State} {s : State}
    (hK : Keys nr w s) (hI : RInv [.v0] w x 1 s) (hm : middle + 2 = nr) :
    WP isa (tail middle) s fun s' => st (s'.v .v0 ^^^ s'.v .v30) = Spec.Aes.cipher nr w (x .v0) ∧ VFrame [.v0] s s' := by
  have br : BlockRegs [.v0] := ⟨by decide, by decide⟩
  refine WP.seq (WP.mono (rounds_tail_ok hK hI middle (by omega_arith)) fun s₁ ⟨hI₁, hf₁⟩ => ?_)
  have hI' : RInv [.v0] w x (nr - 1) s₁ := by
    rwa [show middle + 1 = nr - 1 by omega_arith] at hI₁
  exact WP.mono (folded_last_ok (hK.of_frame hf₁ br) hI')
    fun s' ⟨hv, hf'⟩ => ⟨hv, hf₁.trans hf'⟩

theorem advance_ok (s : State) : WP isa (.block advance) s fun s' =>
    s'.gpr .x3 = s.gpr .x3 + 16 ∧ s'.gpr .x4 = s.gpr .x4 - 1 ∧
    Fr [.x3, .x4] [] s s' := by
  rw [advance, WP.block_cons_iff]
  refine ⟨_, exec_addImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  refine ⟨by simp [State.write, State.read], by simp [State.write, State.read],
    ⟨?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩
  intro r hr
  simp only [List.mem_cons, not_or] at hr
  simp [State.write, hr.1, hr.2]

theorem body_ok {s₀ : State} (hp : UPre s₀) {middle : Nat} (hm : middle + 2 = R s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : Inv s₀ k s) : WP isa (body middle) s (Inv s₀ (k + 1)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 0) 16 := by
    rw [h.rd, h.wr, h.x3, BitVec.add_zero, hp.rd]
    exact ⟨dataR s₀, by simp, Offset.contains_base _ (by omega_arith) (by have := hp.data_wrap; omega_arith)⟩
  refine WP.seq (WP.mono (absorb_ok s hin h.keys h.combo) fun s₁ ⟨e₁, f₁⟩ => ?_)
  have br : BlockRegs [.v0, .v1] := ⟨by decide, by decide⟩
  refine WP.seq (WP.mono (tail_ok (h.keys.of_frame f₁ br) e₁ hm) fun s₂ ⟨e₂, f₂⟩ => ?_)
  refine WP.mono (advance_ok s₂) fun s₃ ⟨e3, e4, f₃⟩ => ?_
  have fv := f₁.trans (f₂.mono (by simp))
  have g : ∀ r, s₂.gpr r = s.gpr r := fun r => by rw [f₂.gpr, f₁.gpr]
  refine ⟨(h.keys.of_frame fv br).of_fr f₃ (by decide) (by decide) ⟨List.nodup_nil, by simp⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₃.v _ (by simp), f₃.v _ (by simp), f₃.v _ (by simp), fv.v _ (by decide), fv.v _ (by decide), fv.v _ (by decide)]
    exact h.combo
  · rw [f₃.gpr _ (by decide), g, h.x2]
  · rw [e3, g, h.x3]
    change Dp s₀ + BitVec.ofNat 64 (16 * k) + BitVec.ofNat 64 16 = _
    exact Offset.add_add_eq _ (by omega_arith)
  · rw [e4, g, h.x4]
    change BitVec.ofNat 64 (N s₀ - k) - BitVec.ofNat 64 1 = _
    rw [Offset.ofNat_sub_ofNat (by omega_arith)]
    congr 1
  · rw [f₃.mem, f₂.mem, f₁.mem, h.mem]
  · rw [f₃.rd, f₂.rd, f₁.rd, h.rd]
  · rw [f₃.wr, f₂.wr, f₁.wr, h.wr]
  · rw [show s₃.v .v0 = s₂.v .v0 from f₃.v _ (by simp),
      show s₃.v .v30 = s₂.v .v30 from f₃.v _ (by simp)]
    change (st (s₂.v .v0 ^^^ s₂.v .v30)).toList = _
    rw [e₂]
    rw [← state_bytes, bytes_xor, h.state, h.mem, h.x3, bytes_read,
      take_succ_blks s₀ hk, Proof.Cmac.chain_append, Proof.Cmac.chain_single]
    rfl

theorem eval_count {s : State} {n : Nat} (hn : n < 2 ^ 64)
    (h : s.gpr .x4 = BitVec.ofNat 64 n) :
    isa.eval (.nonzero .x .x4) s = some !decide (n = 0) := by
  show some (s.read .x .x4 != 0) = _
  rw [State.read, h, BitVec.setWidth_eq, ofNat_ne_zero hn]

theorem loop_ok {s₀ : State} (hp : UPre s₀) {middle : Nat} (hm : middle + 2 = R s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : Inv s₀ k s) : WP isa (.loop (body middle) (.nonzero .x .x4)) s (Inv s₀ (N s₀)) := by
  refine WP.loop (M := isa) (fun (n : Nat) (t : State) =>
    ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ Inv s₀ j t) ?_ (N s₀ - k) s ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok hp hm hk h) fun s' h' => ?_
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  have ev := eval_count (n := N s₀ - (k + 1)) (by omega_arith) h'.x4
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega_arith]
  · right
    exact ⟨by rw [ev]; simp [hz], N s₀ - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, h'⟩

theorem loops_ok {s₀ : State} (hp : UPre s₀) {s : State}
    (hn : 0 < N s₀) (h : Inv s₀ 0 s) : WP isa loops s (Inv s₀ (N s₀)) := by
  have hx6 := h.keys.x6
  have hx7 := h.keys.x7
  obtain h10 | h12 | h14 := h.keys.rounds
  · rw [h10] at hx6
    exact WP.ite true (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun _ => loop_ok hp (by omega_arith) hn h) (fun h => absurd h (by decide))
  · rw [h12] at hx6 hx7
    refine WP.ite false (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun h => absurd h (by decide)) fun _ => ?_
    exact WP.ite true (by simp only [AArch64.eval, State.read, hx7]; decide)
      (fun _ => loop_ok hp (by omega_arith) hn h) (fun h => absurd h (by decide))
  · rw [h14] at hx6 hx7
    refine WP.ite false (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun h => absurd h (by decide)) fun _ => ?_
    exact WP.ite false (by simp only [AArch64.eval, State.read, hx7]; decide)
      (fun h => absurd h (by decide)) (fun _ => loop_ok hp (by omega_arith) hn h)

theorem store_bytes (m : Mem) (p : Addr) (v : BitVec 128) :
    Spec.Aes.bytesAt (m.write p 16 v) p 16 = bytes v := by
  apply List.ext_getElem
  · simp [Spec.Aes.bytesAt, bytes]
  · intro i hi hj
    have hi' : i < 16 := by simpa [Spec.Aes.bytesAt] using hi
    simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, bytes, Vector.getElem_toList, st, Vector.getElem_ofFn, vbyte]
    change (if (p + BitVec.ofNat 64 i - p).toNat < 16 then _ else _) = _
    rw [Mem.sub_ofNat_toNat p (by omega_arith), ite_eq_left hi']

theorem correct_wp {s₀ : State} (hp : UPre s₀) : WP isa update s₀ (updateAArch64.post s₀) := by
  have ev : isa.eval (.zero .x .x4) s₀ = some (decide (N s₀ = 0)) := by
    show some (s₀.read .x .x4 == 0) = _
    rw [State.read, BitVec.setWidth_eq, x4_ofNat]
    have e := ofNat_ne_zero ((s₀.gpr .x4).isLt)
    rw [bne] at e
    cases hb : (BitVec.ofNat 64 (N s₀) == 0) <;> cases hd : decide (N s₀ = 0) <;> simp_all
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    simp [updateAArch64, Spec.Cmac.blocksAt, hn, Spec.Cmac.chain]
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    refine WP.seq (WP.mono (setup_ok hp) fun s₁ h₁ => ?_)
    refine WP.seq (WP.mono (loops_ok hp (by omega_arith) h₁) fun s₂ h₂ => ?_)
    rw [WP.block_cons_iff]
    refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]
    refine ⟨_, exec_strq (off := 0) (by decide) (by
      simp only [State.setV]
      rw [h₂.wr, h₂.x2, BitVec.add_zero, hp.wr]
      exact ⟨stR s₀, by simp, Region.contains_self _ _⟩), WP.block_nil ?_⟩
    change Spec.Aes.bytesAt (s₂.mem.write (s₂.gpr .x2 + 0) 16 (s₂.v .v0 ^^^ s₂.v .v30)) (St s₀) 16 = _
    change Spec.Aes.bytesAt (s₂.mem.write (s₂.gpr .x2 + BitVec.ofNat 64 0) 16 (s₂.v .v0 ^^^ s₂.v .v30)) (St s₀) 16 = _
    rw [h₂.x2, BitVec.add_zero, store_bytes, h₂.state,
      List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

theorem correct (s : State) (hs : updateAArch64.pre s) :
    ∃ t s', Exec isa update s t s' ∧ abiPreserved s s' ∧ updateAArch64.post s s' := by
  obtain ⟨t, s', he, hq, hg⟩ := WP.gprs (rs := preserved) (correct_wp (UPre.of hs))
    (by decide +kernel) (by decide +kernel)
  exact ⟨t, s', he, ⟨hg, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, hq⟩

theorem ct : ConstantTime isa updateAArch64.pre updateAArch64.pub update := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.CmacAes.AArch64.Aese
