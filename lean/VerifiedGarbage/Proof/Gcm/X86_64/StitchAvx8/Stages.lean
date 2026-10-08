import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Work

/-!
# The invariant between AES rounds

`nc` counter slots and `nh` hash inputs have been consumed. Only the two
scratch buffers and `rax` may change between rounds. AES's state registers
and round-key register are absent from the invariant.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB)
open VG.Impl.Gcm.X86_64.StitchAvx8 (aregs prepCounter gh8 prepare reduceFinal)
open VG.Spec.Gcm (Block)

structure StageInv (s₀ start : State) (P X Y : Nat → Block) (y : Block)
    (c nc nh : Nat) (finished : Bool) (s : State) : Prop where
  env : Env s₀ P s
  templates : Templates s₀ c nc s.mem
  prepared : Prepared s₀ X Y nh s.mem
  hash : s.lane .xmm2 0 = if finished then reduceB (accN X P y 8) else y
  product : finished = false → nh ≠ 0 → prod (s.proj 0) = accN X P y nh
  regs : ∀ r, r ≠ .rax → s.gpr r = start.gpr r
  frame : Frame [workR s₀] start.mem s.mem

theorem StageInv.yframe {s₀ start s t : State} {P X Y : Nat → Block} {y : Block}
    {c nc nh : Nat} {finished : Bool} (h : StageInv s₀ start P X Y y c nc nh finished s)
    (hf : YFrame (.xmm1 :: aregs) s t) : StageInv s₀ start P X Y y c nc nh finished t := by
  refine ⟨h.env.yframe hf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf.mem]; exact h.templates
  · rw [hf.mem]; exact h.prepared
  · rw [hf.lane .xmm2 (by decide) 0 (by decide)]; exact h.hash
  · intro hfin hn
    have hp := h.product hfin hn
    simpa only [prod, State.proj_xmm,
      hf.lane .xmm8 (by decide) 0 (by decide), hf.lane .xmm9 (by decide) 0 (by decide),
      hf.lane .xmm10 (by decide) 0 (by decide)] using hp
  · intro r hr; rw [hf.gpr]; exact h.regs r hr
  · rw [hf.mem]; exact h.frame

theorem counter_sub_work (s₀ : State) : Region.Sub (counterR s₀) (workR s₀) :=
  Offset.sub (pp s₀) (d := 640) (e := 512) (n := 128) (k := 256) (by decide) (by decide)

theorem hash_sub_work (s₀ : State) : Region.Sub (hashR s₀) (workR s₀) :=
  Offset.sub (pp s₀) (d := 512) (e := 512) (n := 128) (k := 256) (by decide) (by decide)

theorem hash_counter_disjoint (s₀ : State) : (hashR s₀).Disjoint (counterR s₀) :=
  Offset.disjoint (pp s₀) (d := 512) (e := 640) (n := 128) (k := 128)
    (by decide) (by decide) (by decide)

theorem work_sub_p (s₀ : State) : Region.Sub (workR s₀) (pR s₀) :=
  Offset.sub_base (pp s₀) (d := 512) (n := 256) (k := 1024) (by decide)

theorem StageInv.counters {s₀ start s : State} {P X Y : Nat → Block} {y : Block}
    {c nc nh : Nat} {finished : Bool} (hp : SPre s₀)
    (h : StageInv s₀ start P X Y y c nc nh finished s) (k : Nat) (hk : nc + k ≤ 8)
    (hv : (start.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8)) :
    WP isa (.block ((List.range k).flatMap fun i => prepCounter (nc + i))) s fun t =>
      StageInv s₀ start P X Y y c (nc + k) nh finished t ∧ FlowFrame ghRegs s t := by
  refine WP.mono (prepTemplates_ok hp c nc k hk s h.env h.templates (by
    rw [h.regs .r8 (by decide)]; exact hv)) fun t ⟨hEt, hTt, hf, hm⟩ => ?_
  refine ⟨⟨hEt, hTt, h.prepared.frame hm ?_, ?_, ?_, ?_, ?_⟩, .of_buffer _ hf⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hash_counter_disjoint s₀
  · rw [hf.lane]; exact h.hash
  · intro hfin hn
    have ha := h.product hfin hn
    simpa only [prod, State.proj_xmm, hf.lane] using ha
  · intro r hr; rw [hf.gpr r hr]; exact h.regs r hr
  · refine h.frame.trans (hm.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨workR s₀, List.mem_singleton_self _, counter_sub_work s₀⟩

theorem StageInv.hashStep {s₀ start s : State} {P X Y : Nat → Block} {y : Block}
    {c nc nh : Nat} (hp : SPre s₀) (h : StageInv s₀ start P X Y y c nc nh false s)
    (hn : nh < 8) (more : Bool)
    (hr : more = true → ∀ k < 16, InRegions (s₀.rd ++ s₀.wr)
      (start.gpr .rdx + BitVec.ofNat 64 (16 * k)) 16)
    (hs : more = true → ∀ k < 16, Region.Disjoint
      ⟨start.gpr .rdx + BitVec.ofNat 64 (16 * k), 16⟩ (pR s₀))
    (hx : more = true → ∀ k < 16, Spec.Gcm.blockAt start.mem
      (start.gpr .rdx + BitVec.ofNat 64 (16 * k)) = X k)
    (hY : ∀ i < 8, Y i = if more then X (8 + i) else X i) :
    WP isa (.block (gh8 ((nh + 1) % 8) ++ (if more then prepare (8 + (nh + 1) % 8) else []))) s fun t =>
      StageInv s₀ start P X Y y c nc (nh + 1) false t ∧ FlowFrame ghRegs s t := by
  have hk : (nh + 1) % 8 < 8 := Nat.mod_lt _ (by decide)
  refine WP.mono (hashPrepared_ok hp h.env nh hn h.prepared h.hash (h.product rfl) more
    (fun hm => by rw [h.env.rd, h.env.wr, h.regs .rdx (by decide)]; exact hr hm _ (by omega))
    (fun hm => by rw [h.regs .rdx (by decide)]; exact hs hm _ (by omega))
    (fun hm => ?_) (fun hm i hi => by rw [hY i hi, hm]; rfl))
    fun t ⟨hEt, hBt, hat, hyt, hf, hF⟩ => ?_
  · rw [h.regs .rdx (by decide), hY _ hk, hm]
    exact (VG.Proof.Aes.X86_64.AesNi.blockAt_frame h.frame (fun r hr' => by
      simp only [List.mem_singleton] at hr'
      subst r
      exact (hs hm _ (by omega)).sub_right (work_sub_p s₀))).trans (hx hm _ (by omega))
  · refine ⟨⟨hEt, h.templates.frame hF ?_, hBt, hyt, fun _ _ => hat,
      fun r hr' => (hf.gpr r hr').trans (h.regs r hr'), ?_⟩, hf⟩
    · intro r hr'
      simp only [List.mem_singleton] at hr'
      subst r
      exact (hash_counter_disjoint s₀).symm
    · refine h.frame.trans (hF.sub fun r hr' => ?_)
      simp only [List.mem_singleton] at hr'
      subst r
      exact ⟨workR s₀, List.mem_singleton_self _, hash_sub_work s₀⟩

theorem StageInv.finishHash {s₀ start s : State} {P X Y : Nat → Block} {y : Block}
    {c nc : Nat} (hp : SPre s₀) (h : StageInv s₀ start P X Y y c nc 8 false s) :
    WP isa (.block reduceFinal) s fun t =>
      StageInv s₀ start P X Y y c nc 8 true t ∧ FlowFrame (.xmm1 :: .xmm2 :: ghRegs) s t := by
  refine WP.mono (reduceFinal_ok s (by
    simp only [VG.Proof.Aes.X86_64.AesNi.ea_at, BitVec.ofInt_natCast, h.env.rd, h.env.wr, h.env.r11]
    exact in_rdwr (in_sub hp.p_in (off := 784) (by decide))) (by
    simp only [VG.Proof.Aes.X86_64.AesNi.ea_at, BitVec.ofInt_natCast, h.env.r11]
    exact h.env.poly)) fun t ⟨hv, hf⟩ => ?_
  refine ⟨⟨h.env.yframe hf, ?_, ?_, ?_, fun he => Bool.noConfusion he, ?_, ?_⟩,
    (FlowFrame.of_yframe hf).mono (by decide)⟩
  · rw [hf.mem]; exact h.templates
  · rw [hf.mem]; exact h.prepared
  · rw [hv, h.product rfl (by decide)]; rfl
  · intro r hr; rw [hf.gpr]; exact h.regs r hr
  · rw [hf.mem]; exact h.frame

end VG.Proof.Gcm.X86_64.StitchAvx8
