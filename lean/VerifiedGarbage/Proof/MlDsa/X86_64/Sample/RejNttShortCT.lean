module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttShort
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.SpongeStreamCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Pro
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttShort
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Pro

-- separate module: the relational proofs cost more to check than their imports.

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q G)
open VG.Spec.Sha3 (bytesAt)

namespace RejNttShort

variable {pos : BitVec 64}

open RejNttCT

section
variable {σ₁ σ₂ : State} (hq : rnK.pub σ₁ σ₂)
include hq

theorem pub_X : X σ₁ = X σ₂ := by simp only [X, B, hq.2.2.2.2]
theorem pub_sp : spOf σ₁ pos = spOf σ₂ pos := congrArg (fun P : Sp => {P with prm := pos}) (RejNtt.pub_sp hq)
theorem pub_aP : σ₁.gpr .rsi = σ₂.gpr .rsi := hq.2.1
theorem pub_Lt (t : Nat) : Lt σ₁ t = Lt σ₂ t := by simp only [Lt, pub_X hq]

theorem spPub : SpPub (spOf σ₁ pos) (spOf σ₂ pos) σ₁ σ₂ :=
  ⟨hq.1, rfl, hq.2.2.1, hq.2.1, rfl, hq.2.2.2.1⟩

theorem initPub : SpongeStream.Public (spInit σ₁) (spInit σ₂) σ₁ σ₂ :=
  ⟨hq.1, rfl, hq.2.2.1, hq.2.1, hq.2.2.2.1⟩

end

/-- Two runs at iteration `t`, `n = 260 - t` iterations from the end. -/
def LI (pos : BitVec 64) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂ t, rnK.pre σ₁ ∧ rnK.pre σ₂ ∧ rnK.pub σ₁ σ₂ ∧ n = 260 - t ∧ t < 260 ∧ LAt σ₁ pos t s₁ ∧ LAt σ₂ pos t s₂

theorem bpre {σ : State} (hp : rnK.pre σ) {t : Nat} (ht : t < 260) {s : State} (h : LAt σ pos t s) :
    BPre s (σ.gpr .rsi) (Lt σ t) :=
  ⟨h.env.rbp, h.rdi, Lt_length_le t, .of_mem (by rw [h.env.wr, hp.2.1]; simp), h.stored,
    by simpa using lat_regions hp h (k := 0) (by omega_arith), lat_regions hp h (by omega_arith), lat_regions hp h (by omega_arith)⟩

theorem li_brel {n : Nat} {s₁ s₂ : State} (h : LI pos n s₁ s₂) : BRel s₁ s₂ := by
  obtain ⟨σ₁, σ₂, t, p₁, p₂, hq, _, ht, l₁, l₂⟩ := h
  refine ⟨σ₁.gpr .rsi, Lt σ₁ t, bpre p₁ ht l₁, by rw [pub_aP hq, pub_Lt hq]; exact bpre p₂ ht l₂,
    by rw [l₁.rsi, l₂.rsi, pub_sp hq], by rw [l₁.rcx, l₂.rcx], fun k hk => ?_⟩
  rw [out_byte l₁ (by omega_arith), out_byte l₂ (by omega_arith), pub_X hq]

theorem loop_ct (n : Nat) :
    RelCT isa (LI pos n) (.loop rnBody .ne) (Rel2 rnK.pre rnK.pub fun σ s => LAt σ pos 260 s) := by
  refine RelCT.loop (M := isa) (LI pos) (fun n => ?_) n
  refine RelCT.postDep (F := fun (x x' : State) => ∀ p : State × Nat, rnK.pre p.1 ∧ p.2 < 260 ∧ LAt p.1 pos p.2 x →
      LAt p.1 pos (p.2 + 1) x' ∧ x'.zf = some (BitVec.ofNat 64 (260 - p.2) - 1 == 0))
    (RelCT.mono body_ct (fun x y h => li_brel h) fun _ _ _ => trivial) (fun x y h => ?_) ?_
  · obtain ⟨σ₁, σ₂, t, p₁, p₂, _, _, ht, l₁, l₂⟩ := h
    exact ⟨WP.all' (fun p hp' => lat_step hp'.1 hp'.2.1 hp'.2.2) ⟨(σ₁, t), p₁, ht, l₁⟩,
      WP.all' (fun p hp' => lat_step hp'.1 hp'.2.1 hp'.2.2) ⟨(σ₂, t), p₂, ht, l₂⟩⟩
  · intro x y x' y' ⟨σ₁, σ₂, t, p₁, p₂, hq, hn, ht, l₁, l₂⟩ f₁ f₂
    obtain ⟨l₁', z₁⟩ := f₁ (σ₁, t) ⟨p₁, ht, l₁⟩
    obtain ⟨l₂', z₂⟩ := f₂ (σ₂, t) ⟨p₂, ht, l₂⟩
    have ez : (BitVec.ofNat 64 (260 - t) - 1 == 0) = decide (t + 1 = 260) := by
      rw [ofNat64_pred (by omega_arith) (by omega_arith), ofNat64_beq_zero (by omega_arith)]
      exact decide_eq_decide.mpr (by omega_arith)
    rw [ez] at z₁ z₂
    refine ⟨by show x'.zf.map _ = y'.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht' => ?_⟩
    · have : t + 1 = 260 := by
        have : x'.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [this] at l₁' l₂'
      exact ⟨σ₁, σ₂, p₁, p₂, hq, l₁', l₂'⟩
    · have : t + 1 ≠ 260 := by
        have : x'.zf.map (!·) = some true := ht'
        rw [z₁] at this; simpa using this
      exact ⟨260 - (t + 1), by omega_arith, σ₁, σ₂, t + 1, p₁, p₂, hq, rfl, by omega_arith, l₁', l₂'⟩

/-- After the first block of the loop's setup. -/
def IA (σ : State) (pos : BitVec 64) (s : State) : Prop :=
  Env (spOf σ pos) σ s ∧ bytesAt s.mem ((spOf σ pos).at' 840) 780 = X σ ∧ s.gpr .rsi = (spOf σ pos).at' 840 ∧
    s.gpr .rdi = 0 ∧ SpongeStream.Stream 168 780 (spOf σ pos) σ pos s

theorem latB {σ s : State} (h : IA σ pos s) : WP isa (.block [.mov32 .rcx (.imm 260)]) s (LAt σ pos 0) := by
  refine WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 260)
    (by xrun) (by decide)) fun s2 ⟨⟨hm2, hcx⟩, k2⟩ => ?_
  exact ⟨h.1.keep hm2 (k2.mono (by decide)), by rw [hm2]; exact h.2.1, by rw [k2.gpr (by decide), h.2.2.1]; simp,
    by rw [k2.gpr (by decide), h.2.2.2.1]; rfl, hcx, by rw [hm2]; exact stored_nil _ _, h.2.2.2.2.mem_eq hm2⟩

theorem hok : ∀ σ, rnK.pre σ → SpOk (spOf σ pos) σ := fun _ hp => spOk hp

theorem hpub : ∀ σ₁ σ₂, rnK.pre σ₁ → rnK.pre σ₂ → rnK.pub σ₁ σ₂ → SpPub (spOf σ₁ pos) (spOf σ₂ pos) σ₁ σ₂ :=
  fun _ _ _ _ hq => spPub hq

/-- The prefix loop leaves a state used by the success test. -/
theorem prefix_ct : RelCT isa (Rel2 rnK.pre rnK.pub fun σ s => J6 168 780 (spOf σ pos) σ s ∧ SpongeStream.Stream 168 780 (spOf σ pos) σ pos s)
    (rnLoopCount 260) (Rel2 rnK.pre rnK.pub fun σ => LAt σ pos 260) := by
  refine RelCT.seq (relInv (I' := fun σ => IA σ pos) (fun σ s _ h => lat0 h.1 h.2)
      (taintSp hpub (J := fun P σ s => J6 168 780 P σ s ∧ SpongeStream.Stream 168 780 P σ pos s)
        (fun _ _ h => h.1.env) [] nil_regs (by taint_decide)))
    (RelCT.seq (RelCT.mono (relInv (I' := fun σ s => LAt σ pos 0 s) (fun σ s _ h => latB h)
        (taintSp hpub (J := fun P σ s => Env P σ s ∧ bytesAt s.mem ((spOf σ pos).at' 840) 780 = X σ ∧
          s.gpr .rsi = (spOf σ pos).at' 840 ∧ s.gpr .rdi = 0 ∧ SpongeStream.Stream 168 780 P σ pos s) (fun _ _ h => h.1) [] nil_regs (by taint_decide)))
      (fun _ _ h => h) fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, l₁, l₂⟩ => ⟨σ₁, σ₂, 0, p₁, p₂, hq, rfl, by omega_arith, l₁, l₂⟩)
      (loop_ct 260))

structure Ready (σ : State) (pos : BitVec 64) (s : State) : Prop where
  lat : LAt σ pos 260 s
  zf : s.zf = some (BitVec.ofNat 64 (Lt σ 260).length == 256)

abbrev RR (I : State → State → Prop) := Rel2 rnK.pre rnK.pub I

theorem ready_ok {σ s : State} (h : LAt σ pos 260 s) :
    WP isa (.block [.alu .cmp .rdi (.imm 256)]) s (Ready σ pos) := by
  refine WP.mono (WP.keep [.rdi] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rdi = s.gpr .rdi ∧
      s'.zf = some (s.gpr .rdi - 256 == 0)) (by xrun; rfl) (by decide))
    fun s' ⟨⟨hm, hd, hz⟩, hk⟩ => ?_
  refine ⟨⟨h.env.keep hm (hk.mono (by decide)), by rw [hm]; exact h.out,
    (hk.gpr (by decide)).trans h.rsi, hd.trans h.rdi, (hk.gpr (by decide)).trans h.rcx,
    by rw [hm]; exact h.stored, h.stream.mem_eq hm⟩, ?_⟩
  rw [hz, h.rdi]
  congr 1
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, BitVec.sub_eq_iff_eq_add]
  rfl

theorem cmp_ct : RelCT isa (RR fun σ => LAt σ pos 260)
    (.block [.alu .cmp .rdi (.imm 256)]) (RR fun σ => Ready σ pos) :=
  relInv (fun _ _ _ h => ready_ok h) (taintRel [] nil_regs (by taint_decide))

theorem continue_ct : RelCT isa (RR fun σ => Ready σ pos) rnContinue (fun _ _ => True) := by
  refine RelCT.seq (relInv (I' := fun σ => RejNtt.LAt σ 260)
    (fun σ s hp h => continue_args_ok hp h.lat) ?_)
    (RelCT.seq (RelCT.mono (RejNtt.loop_ct 76) ?_ (fun _ _ h => h)) ?_)
  · refine RelCT.seq (RelCT.mono (SpongeStream.count_ct hok hpub (rate := 168) (done := 780) (pos := pos)) ?_ (fun _ _ h => h))
      (RelCT.seq (SpongeStream.more_ct hok hpub (rate := 168) (offset := 1620) (len := 228) (done := 780) (pos := pos)
        (.inr rfl) (by decide) (fun _ _ => rfl) (by decide) (by taint_decide))
        (taintSp hpub (J := fun P σ s => Env P σ s) (fun _ _ h => h) [] nil_regs (by taint_decide)))
    intro x y ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩
    exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁.lat.env, h₁.lat.stream⟩, ⟨h₂.lat.env, h₂.lat.stream⟩⟩
  · intro x y ⟨σ₁, σ₂, p₁, p₂, hq, l₁, l₂⟩
    exact ⟨σ₁, σ₂, 260, p₁, p₂, hq, rfl, by decide, l₁, l₂⟩
  · exact taintSp RejNtt.hpub (c := .block (retJ ++ epi))
      (J := fun _ σ s => RejNtt.LAt σ 336 s) (fun _ _ h => h.env) [] nil_regs (by taint_decide)

theorem finish_ct : RelCT isa (RR fun σ => LAt σ pos 260)
    (.seq (.block [.alu .cmp .rdi (.imm 256)])
      (.ite .e (.block (retJ ++ epi)) rnContinue)) (fun _ _ => True) := by
  refine RelCT.seq cmp_ct (RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ => ?_) ?_ ?_)
  · show x.zf = y.zf
    rw [h₁.zf, h₂.zf, pub_Lt hq]
  · exact RelCT.mono (taintSp hpub (J := fun _ σ s => Ready σ pos s)
      (fun _ _ h => h.lat.env) [] nil_regs (by taint_decide)) (fun _ _ h => h.1) (fun _ _ h => h)
  · exact RelCT.mono continue_ct (fun _ _ h => h.1) (fun _ _ h => h)

theorem ct : ConstantTime isa rnK.pre rnK.pub rejNTTShort := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (relInv (I' := fun σ => J0 (spInit σ) σ)
    (fun σ s hp h => by subst h; exact pro_ok hp)
    (taintRel [.rdi, .rsi, .rdx, .rsp] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1]) (by taint_decide))) ?_)
  refine RelCT.seq (SpongeStream.stream_ct (fun _ h => initOk h) (fun _ _ _ _ h => initPub h)
    (.inr rfl) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  apply RelCT.exists_
  intro pos
  exact RelCT.seq (prefix_ct (pos := pos)) (finish_ct (pos := pos))

theorem verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Sample.rejNTTShort (Proof.MlDsa.rejNTTContract X86_64.abi 16) :=
  Verified.of_correct correct ct
    { pre := by sig_implies_pre [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, rnK, X86_64.abi,
        X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, rnK, X86_64.abi, X86_64.argRegs]
        dsimp only [rnK] at h
        obtain ⟨hr, hp⟩ := h
        by_cases hf : (rnFold [] (G (bytesAt s.mem (s.gpr .rdi) 34) 1008)).length = 256
        · rw [ifT hf] at hr
          obtain ⟨hred, hpoly⟩ := hp hf
          exact ⟨fun _ => hred, .inl ⟨hr, { Spec.MlDsa.minBounds with rejNTT := 1008 }, by
            show Spec.MlDsa.rejNTTPoly 1008 _ = _
            rw [rejNTT_some hf, hpoly]⟩⟩
        · rw [ifF hf] at hr
          exact ⟨fun h1 => absurd (hr.symm.trans h1) (by decide),
            .inr ⟨hr, rejNTT_none (B := 1008) (by decide) (by decide) hf⟩⟩
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, rnK, X86_64.abi, X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx⟩ := h
        exact ⟨hdi, hsi, hdx, hsp, leakBytes_inj hb⟩
      sat := by sig_implies_sat [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, rnK, X86_64.abi,
        X86_64.argRegs] [rnSat] using rnSat }

end RejNttShort
end VG.Proof.MlDsa.X86_64.Sample
