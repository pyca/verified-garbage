module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Sponge
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Squeeze
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Sponge
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Squeeze
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

-- separate module: continuation and relational proofs cost more than their imports.

@[expose] public section
namespace VG.Proof.MlDsa.X86_64.Sample
open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Spec.Sha3 (stateAt bytesAt squeezeFrom)
open VG.Proof.MlDsa.Sample (padded)

namespace SpongeStream

theorem sp_param {P : Sp} {σ : State} (h : SpOk P σ) (v : BitVec 64) : SpOk {P with prm := v} σ :=
  ⟨h.rd, h.wr, h.sd_a, h.sd_scr, h.a_scr, h.ret_sd, h.ret_a, h.ret_scr,
    h.stk_sd, h.stk_a, h.stk_scr, h.scr_end, h.len_lt⟩

/-- The pointers needed while the parameter register is unused. -/
structure Public (P₁ P₂ : Sp) (σ₁ σ₂ : State) : Prop where
  sd : P₁.sd = P₂.sd
  len : P₁.len = P₂.len
  scr : P₁.scr = P₂.scr
  a : P₁.a = P₂.a
  rsp : σ₁.gpr .rsp = σ₂.gpr .rsp

/-- Splitting the output of one sponge does not repeat any bytes. -/
theorem squeeze_append {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200)
    (st : Spec.Sha3.State) (pos a b : Nat) :
    squeezeFrom rate st pos (a + b) = squeezeFrom rate st pos a ++ squeezeFrom rate st (pos + a) b := by
  apply List.ext_getElem
  · rw [List.length_append, Proof.Sha3.length_squeezeFrom hr hr',
      Proof.Sha3.length_squeezeFrom hr hr', Proof.Sha3.length_squeezeFrom hr hr']
  · intro i hi _
    have hilen : i < a + b := by simpa only [Proof.Sha3.length_squeezeFrom hr hr'] using hi
    simp only [List.getElem_append, Proof.Sha3.length_squeezeFrom hr hr']
    split
    · rename_i ha
      rw [Proof.Sha3.squeezeFrom_getElem hr hr' _ hilen, Proof.Sha3.squeezeFrom_getElem hr hr' _ ha]
    · rename_i ha
      rw [Proof.Sha3.squeezeFrom_getElem hr hr' _ hilen,
        Proof.Sha3.squeezeFrom_getElem hr hr' _ (show i - a < b by omega_arith),
        show pos + a + (i - a) = pos + i by omega_arith]

/-- The saved position and remaining SHAKE stream. -/
structure Stream (rate consumed : Nat) (P : Sp) (σ : State) (pos : BitVec 64) (s : State) : Prop where
  bound : pos.toNat ≤ rate
  next : ∀ d, squeezeFrom rate (stateAt s.mem P.scr) pos.toNat d =
    squeezeFrom rate (padded rate Spec.Sha3.shakeSuffix (P.msg σ)) consumed d

structure Output (rate len : Nat) (P : Sp) (σ s : State) : Prop extends J6 rate len P σ s where
  bound : (s.gpr .rax).toNat ≤ rate
  next : ∀ d, squeezeFrom rate (stateAt s.mem P.scr) (s.gpr .rax).toNat d =
    squeezeFrom rate (padded rate Spec.Sha3.shakeSuffix (P.msg σ)) len d

/-- Full squeeze postcondition, including its continuation state. -/
theorem squeeze_state_call {s : State} {st out scr : Addr} {rate pos len : Nat}
    (h : SqueezeArgs s st out scr rate pos len)
    (hc : Covers ([] ++ [⟨st, 200⟩, ⟨out, len⟩, ⟨scr, 640⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨out, len⟩, ⟨scr, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨out, len⟩, ⟨scr, 640⟩, below (s.gpr .rsp) 16] s.mem s'.mem →
      bytesAt s'.mem out len = squeezeFrom rate (stateAt s.mem st) pos len →
      (s'.gpr .rax).toNat ≤ rate →
      (∀ d, squeezeFrom rate (stateAt s'.mem st) (s'.gpr .rax).toNat d =
        squeezeFrom rate (stateAt s.mem st) (pos + len) d) → Q s') :
    WP isa (.call "vg_keccak_squeeze_scratch" Impl.Sha3.X86_64.Stream.squeeze) s Q := by
  have hr := rate_lt h.hrate
  refine WP.call (k := Proof.Sha3.squeezeX86_64) Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct squeeze_nosp
    (by rw [squeeze_depth]; decide) (squeeze_pre h) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hout, hpos, hnext⟩
  simp only [State.withRegions_gpr, State.withRegions_mem, ce_gpr s (by decide : Reg.rdi ≠ .rsp),
    ce_gpr s (by decide : Reg.rsi ≠ .rsp), ce_gpr s (by decide : Reg.rdx ≠ .rsp),
    ce_gpr s (by decide : Reg.rcx ≠ .rsp), ce_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx,
    h.r8, hm₂, ofNat_toNat' h.hlen, ofNat_toNat' hr,
    ofNat_toNat' (Nat.lt_of_le_of_lt h.hpos hr), hg₂ .rax (by decide), callEntry_stateAt s h.k_st] at hout hpos hnext
  exact hQ s' hrd hwr hcs (by rw [squeeze_depth] at hf; simpa using hf) hout hpos hnext

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem call_ok {rate outlen : Nat} (ho : 840 + outlen ≤ 2024) {s : State} (h : J5 rate outlen P σ s) :
    WP isa (.call "vg_keccak_squeeze_scratch" Impl.Sha3.X86_64.Stream.squeeze) s (Output rate outlen P σ) := by
  obtain ⟨h, hargs⟩ := h
  have cov := covS hp ho h.env
  have sub : ∀ r ∈ [(⟨P.scr, 200⟩ : Region), ⟨P.at' 840, outlen⟩, ⟨P.at' 200, 640⟩],
      Region.Sub r ⟨P.scr, 2024⟩ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [Region.sub_prefix (by omega_arith), Offset.sub_base _ (by omega_arith), Offset.sub_base _ (by omega_arith)]
  refine squeeze_state_call hargs cov.1 cov.2 fun s' hrd hwr hcs hf hout hpos hnext => ?_
  refine ⟨⟨Env.call hp h.env sub hrd hwr hcs hf, ?_⟩, hpos, ?_⟩
  · rw [hout, h.st]
  · intro d; rw [hnext, h.st, Nat.zero_add]

theorem sponge_ok {rate outlen : BitVec 32} (hr : spRate rate) (ho : 840 + outlen.toNat ≤ 2024) {s : State}
    (h : J0 P σ s) : WP isa (sponge rate outlen) s (Output rate.toNat outlen.toNat P σ) :=
  WP.seq (WP.mono (blk1_ok hp hr h) fun _ h1 =>
    WP.seq (WP.mono (call1_ok hp h1) fun _ h2 => WP.seq (WP.mono (blk2_ok hp hr h2) fun _ h3 =>
      WP.seq (WP.mono (call2_ok hp h3) fun _ h4 => WP.seq (WP.mono (blk3_ok hp hr ho h4) fun _ h5 =>
        call_ok hp ho h5)))))

/-- A store in the bookkeeping area preserves the sampler environment. -/
theorem store_env {s s' : State} (he : Env P σ s) {k : Nat} (hk : k + 8 ≤ 2024) {v : BitVec 64}
    (hm : s'.mem = s.mem.writeW (P.at' k) v) (hg : Keep [] s s') : Env P σ s' := by
  have hf : Frame [⟨P.at' k, 8⟩] s.mem s'.mem := by
    rw [hm]; exact Frame.writeW (Frame.refl _ _) (by simp) _ (Region.contains_self _ _)
  exact Env.call hp he (rs := [⟨P.at' k, 8⟩]) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ hk)
    hg.2.1 hg.2.2 (fun r _ => hg.gpr (by simp)) (hf.mono (fun _ h => by simp only [List.mem_singleton] at h; subst h; simp))

omit hp in
theorem Stream.frame {rate consumed : Nat} {pos : BitVec 64} {s s' : State}
    (h : Stream rate consumed P σ pos s) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hst : ∀ r ∈ rs, (⟨P.scr, 200⟩ : Region).Disjoint r)
    : Stream rate consumed P σ pos s' := by
  have hs : stateAt s'.mem P.scr = stateAt s.mem P.scr :=
    Proof.Sha3.stateAt_congr fun j hj => hf.bytes hst (by show (200 : Nat) ≤ 2 ^ 64; decide) hj
  exact ⟨h.bound, by rw [hs]; exact h.next⟩

omit hp in
/-- Changing the parameter register leaves the rest of the layout intact. -/
theorem env_param {s s' : State} (h : Env P σ s) {v : BitVec 64}
    (hm : s'.mem = s.mem) (hk : Keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12] s s') (hv : s'.gpr .r12 = v) :
    Env {P with prm := v} σ s' := by
  refine ⟨hk.2.1.trans h.rd, hk.2.2.trans h.wr, (hk.gpr (by decide)).trans h.rbx,
    (hk.gpr (by decide)).trans h.rbp, hv, (hk.gpr (by decide)).trans h.rsp, ?_, ?_, ?_⟩
  · intro r hr
    have hn : r ∉ [Reg.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide
    exact (hk.gpr hn).trans (h.cs r hr)
  · rw [hm]; exact h.saved
  · rw [hm]; exact h.frame

omit hp in
theorem save_ok {rate len : Nat} {s : State} (h : Output rate len P σ s) :
    WP isa (.block savePosition) s fun s' =>
      J6 rate len {P with prm := s.gpr .rax} σ s' ∧ Stream rate len {P with prm := s.gpr .rax} σ (s.gpr .rax) s' := by
  refine WP.mono (WP.keep [.r12] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r12 = s.gpr .rax)
    (by unfold savePosition; xrun) (by decide)) fun s' ⟨⟨hm, hv⟩, hk⟩ => ?_
  refine ⟨⟨env_param h.env hm (hk.mono (by decide)) hv, by rw [hm]; exact h.out⟩,
    ⟨h.bound, by intro d; rw [hm]; exact h.next d⟩⟩

theorem stream_ok {rate outlen : BitVec 32} (hr : spRate rate) (ho : 840 + outlen.toNat ≤ 2008) {s : State}
    (h : J0 P σ s) : WP isa (spongeStream rate outlen) s fun s' =>
      ∃ pos, J6 rate.toNat outlen.toNat {P with prm := pos} σ s' ∧ Stream rate.toNat outlen.toNat {P with prm := pos} σ pos s' := by
  exact WP.seq (WP.mono (sponge_ok hp hr (by omega_arith) h) fun s1 h1 =>
    WP.mono (save_ok h1) fun _ h2 => ⟨s1.gpr .rax, h2⟩)

omit hp in
theorem Stream.mem_eq {rate consumed : Nat} {pos : BitVec 64} {s s' : State}
    (h : Stream rate consumed P σ pos s) (hm : s'.mem = s.mem) : Stream rate consumed P σ pos s' :=
  ⟨h.bound, by intro d; rw [hm]; exact h.next d⟩

theorem count_ok {s : State} (h : Env P σ s) : WP isa (.block saveCount) s fun s' =>
    Env P σ s' ∧ Keep [] s s' ∧ s'.mem.readW (P.at' 2016) 64 = s.gpr .rdi ∧
    Frame [⟨P.at' 2016, 8⟩] s.mem s'.mem := by
  refine WP.mono (WP.keep [] (Q := fun s' => s'.mem = s.mem.writeW (P.at' 2016) (s.gpr .rdi))
    (by unfold saveCount; xrun [h.rbx, inScr hp h (a := 2016) (n := 8) (by decide)]) (by decide))
    fun s' ⟨hm, hk⟩ => ?_
  refine ⟨store_env hp h (by decide) hm hk, hk, ?_, ?_⟩
  · rw [hm, Mem.readW_writeW_self64]
  · rw [hm]; exact Frame.writeW (Frame.refl _ _) (by simp) _ (Region.contains_self _ _)

/-- After setting up a continuation squeeze. -/
structure More (rate done len : Nat) (P : Sp) (σ : State) (pos : BitVec 64) (s : State) : Prop where
  env : Env P σ s
  stream : Stream rate done P σ pos s
  args : SqueezeArgs s P.scr (P.at' (840 + done)) (P.at' 200) rate pos.toNat len

theorem more_args_ok {rate offset len : BitVec 32} {done : Nat} {pos : BitVec 64}
    (hr : spRate rate) (ho : 840 + done + len.toNat ≤ 2008) (hprm : P.prm = pos)
    (hx : BitVec.signExtend 64 offset = BitVec.ofNat 64 (840 + done))
    {s : State} (he : Env P σ s) (hs : Stream rate.toNat done P σ pos s) :
    WP isa (.block (moreArgs rate offset len)) s (fun s' => More rate.toNat done len.toNat P σ pos s' ∧ s'.mem = s.mem) := by
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rdi = P.scr ∧ s'.gpr .rsi = BitVec.ofNat 64 rate.toNat ∧ s'.gpr .rdx = pos ∧
      s'.gpr .rcx = P.at' (840 + done) ∧ s'.gpr .r8 = BitVec.ofNat 64 len.toNat ∧ s'.gpr .r9 = P.at' 200)
    (by unfold moreArgs; xrun [he.rbx, he.r12, hprm, hx, sx200, sw64])
    (by rfl)) fun s' ⟨⟨hm, hdi, hsi, hdx, hcx, h8, h9⟩, hk⟩ => ?_
  have e := he.keep hm (hk.mono (by decide))
  refine ⟨⟨e, hs.mem_eq hm, ⟨hdi, hsi, ?_, hcx, h8, h9, spRate_mem hr, hs.bound, ?_,
    disj_scr0 (by omega_arith) (by omega_arith), disj_scr0 (by decide) (by decide),
    (disj_scr (a := 200) (n := 640) (b := 840 + done) (m := len.toNat) (by omega_arith) (by omega_arith)).symm,
    by rw [e.rsp]; exact stk_scr0 hp (by decide), by rw [e.rsp]; exact stk_scr' hp (by omega_arith),
    by rw [e.rsp]; exact stk_scr' hp (by decide)⟩⟩, hm⟩
  · rw [hdx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · exact Nat.lt_trans len.isLt (by decide)

theorem cov_more {done len : Nat} (ho : 840 + done + len ≤ 2008) {s : State} (he : Env P σ s) : Covers ([] ++ [⟨P.scr, 200⟩, ⟨P.at' (840 + done), len⟩, ⟨P.at' 200, 640⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨P.scr, 200⟩, ⟨P.at' (840 + done), len⟩, ⟨P.at' 200, 640⟩] s.wr := by
    refine ⟨cov_all hp he ?_, cov_scr hp he ?_⟩
    all_goals intro r hr; simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    · rcases hr with rfl | rfl | rfl
      exacts [.inr ⟨0, (add_ofNat_zero _).symm, by simp⟩,
        .inr ⟨840 + done, rfl, by simp; omega_arith⟩, .inr ⟨200, rfl, by simp⟩]
    · rcases hr with rfl | rfl | rfl
      exacts [⟨0, (add_ofNat_zero _).symm, by simp⟩,
        ⟨840 + done, rfl, by simp; omega_arith⟩, ⟨200, rfl, by simp⟩]

theorem more_call_ok {rate done len : Nat} {pos : BitVec 64}
    (ho : 840 + done + len ≤ 2008) {s : State} (h : More rate done len P σ pos s) :
    WP isa (.call "vg_keccak_squeeze_scratch" Impl.Sha3.X86_64.Stream.squeeze) s fun s' =>
      Env P σ s' ∧ bytesAt s'.mem (P.at' (840 + done)) len =
        squeezeFrom rate (padded rate Spec.Sha3.shakeSuffix (P.msg σ)) done len ∧
      Frame [⟨P.scr, 200⟩, ⟨P.at' (840 + done), len⟩, ⟨P.at' 200, 640⟩, below (σ.gpr .rsp) 16] s.mem s'.mem := by
  have hc := cov_more hp ho h.env
  have hsub : ∀ r ∈ [(⟨P.scr, 200⟩ : Region), ⟨P.at' (840 + done), len⟩, ⟨P.at' 200, 640⟩],
      Region.Sub r ⟨P.scr, 2024⟩ := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [Region.sub_prefix (by decide), Offset.sub_base _ (by omega_arith), Offset.sub_base _ (by decide)]
  refine squeeze_call h.args hc.1 hc.2 fun s' rd wr cs hf hout =>
    ⟨Env.call hp h.env hsub rd wr cs hf, ?_, by rw [← h.env.rsp]; exact hf⟩
  rw [hout, h.stream.next]


theorem more_ok {rate offset len : BitVec 32} {done : Nat} {pos : BitVec 64}
    (hr : spRate rate) (ho : 840 + done + len.toNat ≤ 2008) (hprm : P.prm = pos)
    (hx : BitVec.signExtend 64 offset = BitVec.ofNat 64 (840 + done))
    {s : State} (he : Env P σ s) (hs : Stream rate.toNat done P σ pos s) :
    WP isa (squeezeMore rate offset len) s fun s' =>
      Env P σ s' ∧ bytesAt s'.mem (P.at' (840 + done)) len.toNat =
        squeezeFrom rate.toNat (padded rate.toNat Spec.Sha3.shakeSuffix (P.msg σ)) done len.toNat ∧
      Frame [⟨P.scr, 200⟩, ⟨P.at' (840 + done), len.toNat⟩, ⟨P.at' 200, 640⟩, below (σ.gpr .rsp) 16] s.mem s'.mem := by
  refine WP.seq (WP.mono (more_args_ok hp hr ho hprm hx he hs) fun _ ⟨h, hm⟩ => ?_)
  exact WP.mono (more_call_ok hp ho h) fun _ ⟨he, ho, hf⟩ => ⟨he, ho, by rw [hm] at hf; exact hf⟩

theorem more_word_apart {done len k : Nat} (ho : 840 + done + len ≤ 2008)
    (hk : 2008 ≤ k) (hk' : k + 8 ≤ 2024) :
    ∀ r ∈ [(⟨P.scr, 200⟩ : Region), ⟨P.at' (840 + done), len⟩, ⟨P.at' 200, 640⟩, below (σ.gpr .rsp) 16],
      (⟨P.at' k, 8⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (disj_scr0 (by omega_arith) (by omega_arith)).symm
  · exact (disj_scr (by omega_arith) (by omega_arith)).symm
  · exact (disj_scr (by omega_arith) (by omega_arith)).symm
  · exact (stk_scr' hp (by omega_arith)).symm

theorem more_prefix_apart {done len : Nat} (ho : 840 + done + len ≤ 2008) :
    ∀ r ∈ [(⟨P.scr, 200⟩ : Region), ⟨P.at' (840 + done), len⟩, ⟨P.at' 200, 640⟩, below (σ.gpr .rsp) 16],
      (⟨P.at' 840, done⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (disj_scr0 (by omega_arith) (by omega_arith)).symm
  · exact disj_scr (by omega_arith) (by omega_arith)
  · exact (disj_scr (by omega_arith) (by omega_arith)).symm
  · exact (stk_scr' hp (by omega_arith)).symm

theorem more_poly_apart {done len : Nat} (ho : 840 + done + len ≤ 2008) :
    ∀ r ∈ [(⟨P.scr, 200⟩ : Region), ⟨P.at' (840 + done), len⟩, ⟨P.at' 200, 640⟩, below (σ.gpr .rsp) 16],
      (pR P.a).Disjoint r := by
  intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [hp.a_scr.sub_right (sub_scr0 (by decide)), a_scr' hp (by omega_arith), a_scr' hp (by decide), hp.stk_a.symm]


end
end SpongeStream
end VG.Proof.MlDsa.X86_64.Sample
