module

import VerifiedGarbage.Proof.Sm4.Arm.CbcPrologue
public import VerifiedGarbage.Proof.Sm4.Arm.BatchPrologue
public import VerifiedGarbage.Proof.Sm4.Arm.CbcHead
public import VerifiedGarbage.Proof.Sm4.Arm.CbcLoop
import VerifiedGarbage.Proof.Sm4.Arm.BatchTaint
import VerifiedGarbage.Proof.Sm4.Arm.CbcTaint
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
public import VerifiedGarbage.Proof.Sm4.Prepared

/-! # Constant-time composition for batched SM4-CBC decryption -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CbcCT

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.CbcHead VG.Proof.Sm4.Arm.CbcLoop
open VG.Proof.Sm4.Arm.BatchPrologue VG.Proof.Sm4.Arm.BatchFill
open VG.Proof.Sm4.Arm.CbcPrologue
open VG.Proof.Sm4.Arm.CbcGroup

theorem append_eq {a b c d : List Leak} (h : a = b) (h' : c = d) : a ++ c = b ++ d := by rw [h, h']

/-- Functional postconditions hold of any execution, by determinism. -/
theorem result {c : Prog isa} {s s' : State} {t : List Leak} {Q : State → Prop}
    (h : WP isa c s Q) (e : Exec isa c s t s') : Q s' := by
  obtain ⟨_, _, e', h'⟩ := h
  obtain ⟨_, rfl⟩ := Exec.det e e'
  exact h'

theorem checked {rs : List Reg} {c : Prog isa}
    (hc : ∃ h, (taint.check (Taint.ofRegs rs) c h).isSome = true)
    {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}
    (hag : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (e₁ : Exec isa c s₁ t₁ s₁') (e₂ : Exec isa c s₂ t₂ s₂') : t₁ = t₂ := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) (P := fun a b => ∀ r ∈ rs, a.gpr r = b.gpr r)
    (Taint.ofRegs rs) (fun _ _ h => Taint.agree_ofRegs h) hc) _ _ _ _ _ _ hag e₁ e₂).1

/-- Reassociate the existing group at the point where the helper returns. -/
theorem group_split {s s' : State} {t : List Leak} (e : Exec isa BatchCbc.group s t s') :
    ∃ m th tt, Exec isa groupHead s th m ∧ Exec isa groupTail m tt s' ∧ t = th ++ tt := by
  cases e with | seq a b =>
    cases b with | seq c d =>
      cases c with | seq f g =>
        cases g with | seq k x =>
          cases x with | seq xx cp =>
            exact ⟨_, _, _, .seq a (.seq f k), .seq xx (.seq cp d), by simp only [List.append_assoc]⟩

theorem group_ct {B I D : BitVec 32} {n : Nat} (hn : 1 ≤ n) (hn32 : n < 2 ^ 32)
    {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}
    (h₁ : HeadPre B I D n s₁) (h₂ : HeadPre B I D n s₂) (hd : s₁.gpr .r6 = s₂.gpr .r6)
    (e₁ : Exec isa BatchCbc.group s₁ t₁ s₁') (e₂ : Exec isa BatchCbc.group s₂ t₂ s₂') : t₁ = t₂ := by
  obtain ⟨m₁, th₁, tt₁, eh₁, et₁, tr₁⟩ := group_split e₁
  obtain ⟨m₂, th₂, tt₂, eh₂, et₂, tr₂⟩ := group_split e₂
  have ht : th₁ = th₂ := checked CbcTaint.groupHead_check (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h₁.iv.trans h₂.iv.symm
    · exact hd
    · rw [h₁.left, h₂.left]
    · exact h₁.base.trans h₂.base.symm) eh₁ eh₂
  have p₁ := result (head_wp hn hn32 h₁) eh₁
  have p₂ := result (head_wp hn hn32 h₂) eh₂
  have tt : tt₁ = tt₂ := checked CbcTaint.groupTail_check (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [p₁.regs _ (by simp), p₂.regs _ (by simp)]; exact h₁.iv.trans h₂.iv.symm
    · rw [p₁.regs _ (by simp), p₂.regs _ (by simp), hd]
    · rw [p₁.regs _ (by simp), p₂.regs _ (by simp), h₁.left, h₂.left]
    · rw [p₁.regs _ (by simp), p₂.regs _ (by simp)]; exact h₁.base.trans h₂.base.symm
    · rw [p₁.group, p₂.group]) et₁ et₂
  rw [tr₁, tr₂, ht, tt]

section
variable {s₀ s₀' : State} {B I D : BitVec 32} {K K' : Spec.Sm4.Schedule} {t t' : List Byte} {n : Nat}
    (hn32 : n < 2 ^ 32) (hB : s₀.gpr sb = B) (hB' : s₀'.gpr sb = B)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hI : s₀.gpr .r5 = I) (hI' : s₀'.gpr .r5 = I) (fitI : I.toNat + 16 ≤ 2 ^ 32)
    (hiv : Covers [⟨State.addr I, 16⟩] s₀.wr) (hiv' : Covers [⟨State.addr I, 16⟩] s₀'.wr)
    (id : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr D, 16 * n⟩)
    (ib : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (hw' : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀'.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (wd' : Covers [⟨State.addr D, 16 * n⟩] s₀'.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)

def LoopRel (s₀ s₀' : State) (B I D : BitVec 32) (K K' : Spec.Sm4.Schedule) (t t' : List Byte)
    (n m : Nat) (a b : State) : Prop :=
  ∃ i, m = n - i ∧ i < n ∧ LoopInv s₀ B I D K t n i a ∧ LoopInv s₀' B I D K' t' n i b

include hn32 hB hB' fitB fitD hI hI' fitI hiv hiv' id ib hw hw' wd wd' sep in
 theorem loop_ct (m : Nat) :
    RelCT isa (LoopRel s₀ s₀' B I D K K' t t' n m) (.loop BatchCbc.group .ne)
      (fun a b => LoopInv s₀ B I D K t n n a ∧ LoopInv s₀' B I D K' t' n n b) := by
  refine RelCT.loop (M := isa) (LoopRel s₀ s₀' B I D K K' t t' n) (fun m => ?_) m
  intro a b ta tb a' b' ⟨i, hm, hi, l, l'⟩ ea eb
  have p := loop_pre hn32 hi hB fitB fitD hI fitI hiv id ib hw wd sep l
  have p' := loop_pre hn32 hi hB' fitB fitD hI' fitI hiv' id ib hw' wd' sep l'
  have eqtr := group_ct (by omega) (by omega) p p' (by rw [l.data, l'.data]) ea eb
  obtain ⟨la, za⟩ := result (loopInv_step hn32 hi hB fitB fitD hI fitI hiv id ib hw wd sep l) ea
  obtain ⟨lb, zb⟩ := result (loopInv_step hn32 hi hB' fitB fitD hI' fitI hiv' id ib hw' wd' sep l') eb
  have evA : isa.eval .ne a' = some !decide (i + min (n - i) 8 = n) := by
    change some (!a'.z) = _; rw [za]
  have evB : isa.eval .ne b' = some !decide (i + min (n - i) 8 = n) := by
    change some (!b'.z) = _; rw [zb]
  refine ⟨eqtr, by rw [evA, evB], ?_, ?_⟩
  · intro h
    rw [evA] at h
    have he : i + min (n - i) 8 = n := by simpa using h
    rw [he] at la lb
    exact ⟨la, lb⟩
  · intro h
    rw [evA] at h
    have he : i + min (n - i) 8 ≠ n := by simpa using h
    refine ⟨n - (i + min (n - i) 8), by omega, i + min (n - i) 8, rfl, ?_, la, lb⟩
    have := la.bound
    omega

include hn32 hB hB' fitB fitD hI hI' fitI hiv hiv' id ib hw hw' wd wd' sep in
 theorem dataLoop_ct :
    RelCT isa (fun a b => LoopInv s₀ B I D K t n 0 a ∧ LoopInv s₀' B I D K' t' n 0 b ∧
      a.z = decide (n = 0) ∧ b.z = decide (n = 0)) BatchCbc.dataLoop (fun _ _ => True) := by
  have ev {a : State} (h : a.z = decide (n = 0)) : isa.eval .eq a = some (decide (n = 0)) := by
    change some a.z = _; rw [h]
  refine RelCT.ite (fun a b h => by rw [ev h.2.2.1, ev h.2.2.2]) ?_ ?_
  · obtain ⟨_, hc⟩ := BatchTaint.nil_check
    exact RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (fun r hr => by simp at hr)) hc
  · refine (loop_ct (K := K) (K' := K') (t := t) (t' := t') hn32 hB hB' fitB fitD hI hI' fitI hiv hiv' id ib hw hw' wd wd' sep n).mono (fun a b h => ?_) (fun _ _ _ => trivial)
    have he := h.2
    rw [ev h.1.2.2.1] at he
    have hn : 0 < n := by
      have : n ≠ 0 := by simpa using he
      omega
    exact ⟨0, by omega, hn, h.1.1, h.1.2.1⟩

end

def Pub (s s' : State) : Prop :=
  s.sp = s'.sp ∧ s.gpr .r0 = s'.gpr .r0 ∧ s.gpr .r1 = s'.gpr .r1 ∧
  s.gpr .r2 = s'.gpr .r2 ∧ s.gpr .r3 = s'.gpr .r3 ∧ Sc s = Sc s'

theorem arg_wf {s : State} (h : BatchPrologue.Pre s) :
    s.sp.toNat + 4 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 4⟩ r := by
  refine ⟨h.spFit, ?_⟩
  intro r hr
  have he : (⟨State.addr s.sp, 4⟩ : Region) = argR s := by simp [argR, stackArgAddr]
  rw [he, h.wr] at *
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h.ia.symm, h.da.symm, h.sa.symm]

theorem prologue_ct {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}
    (h₁ : BatchPrologue.Pre s₁) (h₂ : BatchPrologue.Pre s₂) (hq : Pub s₁ s₂)
    (e₁ : Exec isa BatchCbc.prologue s₁ t₁ s₁') (e₂ : Exec isa BatchCbc.prologue s₂ t₂ s₂') : t₁ = t₂ := by
  cases e₁ with | seq a b =>
    cases b with | seq p u =>
      cases e₂ with | seq a' b' =>
        cases b' with | seq p' u' =>
          have eh := Exec.seq a p
          have eh' := Exec.seq a' p'
          have hag : VG.Arm.Taint.Agree (argTaint [.r0, .r1, .r2, .r3] 4) s₁ s₂ :=
            agree_argTaint (fun r hr => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl | rfl
              exacts [hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1]) hq.1 (arg_wf h₁) (arg_wf h₂)
              (argMem_of (j := 1) hq.1 h₁.spFit (fun i hi => by
                have he : i = 0 := by omega
                subst i
                exact hq.2.2.2.2.2))
          obtain ⟨_, hc⟩ := CbcTaint.proHead_check
          have heq := ((RelCT.taint (A := taint) (P := fun a b => VG.Arm.Taint.Agree (argTaint [.r0, .r1, .r2, .r3] 4) a b)
            (argTaint [.r0, .r1, .r2, .r3] 4) (fun _ _ h => h) hc) _ _ _ _ _ _ hag eh eh').1
          obtain ⟨i, n, b⟩ := result (proHead_wp h₁) eh
          obtain ⟨i', n', b'⟩ := result (proHead_wp h₂) eh'
          have heq' := checked BatchTaint.setup_check (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · rw [i, i']; exact hq.2.2.1
            · rw [n, n']; unfold N; rw [hq.2.2.2.2.1]
            · exact b.trans (hq.2.2.2.2.2.trans b'.symm)) u u'
          simpa only [List.append_assoc] using append_eq heq heq'

theorem initial {s : State} {B I D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n : Nat}
    (hD : s.gpr .r6 = D) (hN : s.gpr .r7 = BitVec.ofNat 32 n)
    (hH : Proof.Sm4.Prepared.Holds layout s.mem (State.addr B) K .decrypt)
    (hC : Spec.Aes.bytesAt s.mem (counterAddr B) 16 = t) : LoopInv s B I D K t n 0 s :=
  ⟨fun _ _ => rfl, by simpa only [Nat.mul_zero, BitVec.add_zero] using hD,
    by simpa only [Nat.sub_zero] using hN, by omega, rfl, rfl, rfl, Frame.refl _ _, hH,
    by change Spec.Aes.bytesAt s.mem (counterAddr B) 16 = t; exact hC, fun _ h => by omega⟩

theorem cbc_ct : ConstantTime isa BatchPrologue.Pre Pub BatchCbc.decrypt := by
  intro s₁ s₂ tr₁ tr₂ s₁' s₂' hp₁ hp₂ hq e₁ e₂
  have eB : Sc s₂ = Sc s₁ := hq.2.2.2.2.2.symm
  have eI : Iv s₂ = Iv s₁ := hq.2.2.1.symm
  have eD : Dp s₂ = Dp s₁ := hq.2.2.2.1.symm
  have eN : N s₂ = N s₁ := by unfold N; rw [hq.2.2.2.2.1]
  have hw₁ := hp₁.writable (r := wsR s₁) (by simp)
  have hw₂ := hp₂.writable (r := wsR s₂) (by simp)
  have hi₁ := hp₁.writable (r := ivR s₁) (by simp)
  have hi₂ := hp₂.writable (r := ivR s₂) (by simp)
  have wd₁ := hp₁.writable (r := dataR s₁) (by simp)
  have wd₂ := hp₂.writable (r := dataR s₂) (by simp)
  cases e₁ with | seq pro rest =>
    cases rest with | seq dl fin =>
      cases e₂ with | seq pro' rest' =>
        cases rest' with | seq dl' fin' =>
          have eqP := prologue_ct hp₁ hp₂ hq pro pro'
          have p := result (CbcPrologue.prologue_wp hp₁) pro
          have p' := result (CbcPrologue.prologue_wp hp₂) pro'
          have pb' := p'.base
          have pi' := p'.iv
          rw [eI] at pi'
          have pd' := p'.data
          have pn' := p'.left
          have pt' := p'.table
          have pc' := p'.counter
          have pz' := p'.z
          rw [eB] at pb' pt' pc'
          rw [eD] at pd'
          rw [eN] at pn' pz'
          have ib := initial (I := Iv s₁) p.data p.left p.table p.counter
          have ib' := initial (I := Iv s₁) pd' pn' pt' pc'
          have w₁ := hw₁
          have w₂ := hw₂
          have d₁ := wd₁
          have d₂ := wd₂
          rw [← p.wr] at w₁ d₁
          rw [← p'.wr] at w₂ d₂
          change Covers [⟨State.addr (Sc s₂), 4 * BatchCtr.totalSlots⟩] _ at w₂
          change Covers [⟨State.addr (Dp s₂), 16 * N s₂⟩] _ at d₂
          rw [eB] at w₂
          rw [eD, eN] at d₂
          have i₁ := hi₁
          have i₂ := hi₂
          rw [← p.wr] at i₁
          rw [← p'.wr] at i₂
          change Covers [⟨State.addr (Iv s₂), 16⟩] _ at i₂
          rw [eI] at i₂
          have rel := dataLoop_ct (K := Spec.Sm4.scheduleAt s₁.mem (State.addr (Kp s₁)))
            (K' := Spec.Sm4.scheduleAt s₂.mem (State.addr (Kp s₂)))
            (t := Spec.Aes.bytesAt s₁.mem (State.addr (Iv s₁)) 16)
            (t' := Spec.Aes.bytesAt s₂.mem (State.addr (Iv s₂)) 16)
            (s₁.gpr .r3).isLt p.base pb' hp₁.fitB hp₁.fitD p.iv pi' hp₁.fitI i₁ i₂ hp₁.id hp₁.ivs w₁ w₂ d₁ d₂ hp₁.ds
          have eqL := (rel _ _ _ _ _ _ ⟨ib, ib', p.z, pz'⟩ dl dl').1
          have l := result (loopOrEmpty_wp (s₁.gpr .r3).isLt p.base p.data p.left p.z hp₁.fitB hp₁.fitD p.iv hp₁.fitI i₁ hp₁.id hp₁.ivs w₁ d₁ hp₁.ds p.table p.counter) dl
          have l' := result (loopOrEmpty_wp (s₁.gpr .r3).isLt pb' pd' pn' pz' hp₁.fitB hp₁.fitD pi' hp₁.fitI i₂ hp₁.id hp₁.ivs w₂ d₂ hp₁.ds pt' pc') dl'
          have eqF := checked BatchTaint.finish_check (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · rw [l.regs _ (by simp), l'.regs _ (by simp), p.iv, p'.iv]; exact hq.2.2.1
            · rw [l.regs _ (by simp), l'.regs _ (by simp)]
              exact p.base.trans pb'.symm) fin fin'
          exact append_eq eqP (append_eq eqL eqF)

end VG.Proof.Sm4.Arm.CbcCT
