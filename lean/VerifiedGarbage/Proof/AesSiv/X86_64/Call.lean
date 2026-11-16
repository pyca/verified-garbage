module

public import VerifiedGarbage.Proof.CmacAes.X86_64.FinalizeCorrect
public import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Call
public import VerifiedGarbage.Proof.AesCcm.X86_64.Callee
public import VerifiedGarbage.Impl.AesSiv.X86_64
import VerifiedGarbage.Proof.AesSiv.X86_64.Common
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-SIV on x86-64: calling `vg_cmac_aes_finalize` with any subkeys

`vg_cmac_aes_finalize`'s contract gives the CMAC of the message only when the
subkeys in its `key` are those of the key schedule's cipher. Its code needs
no such thing: it computes `CIPH_K(C ⊕ Mₙ)` from whatever subkeys `key`
holds, for the chaining value `C` at `state` and the last block `Mₙ` of
§6.2 step 4 (`finalize_raw_wp`). AES-SIV's contracts compute with the
subkeys its key context holds (`Spec.Siv.ctxMac`), so its calls use this
(`finr_call`), with `WP.call` from this correctness of the same code.

## The two layouts of the working space

`encrypt` and `decrypt` are proven once for both layouts of their working
space `W` (`Lay`): over any implementations (`Lay.soft`), the functions they
call are given the scratch pointer `W + 256` and may write the 2176 bytes
there, and S2V's state `D` follows the 2560 bytes of `W`; over
implementations of `vg_aes_ctr32` and `vg_cmac_aes_update` that never touch
their scratch buffer (`Lay.free`), the scratch pointer is `W + 256 - 2048`,
`vg_cmac_aes_finalize` writes only its counter block, the 16 bytes at
`W + 256`, and `D` follows them. In both, what a call may write of `W` starts
at `W + 256`: the proofs need only its length (`Lay.xn`), the arguments of
each call with that part of `W` for its working space (`FA`, `UA`, `CA`,
`WA`), and the calls from them (`CCalls`, `Calls`), which are those of the
callees' contracts with a scratch buffer (`CCalls.soft`, `Calls.soft`) or
without one (`CCalls.free`, `Calls.free`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (FPre finPre_wp finPreF_wp ctr_call ctr_callF ctr_rel ctr_relF ctrCall_ok
  ctrCall_okF bytesAt_frame
  finalizeX86_64 finalizeX86_64F finalize_mx mn CallPre CallPreF CallPostX UpdateImpl UpdateFree updateX86_64
  updateX86_64F toNat_rounds)
open VG.Proof.CmacAes.Stream.X86_64 (FArgs FArgsF UArgs UPostZ finalize_nosp finalize_depth callEntry_bytes
  toNat_ofNat upd_call upd_rel fin_rel fin_relF ret_sub stk_sub)
open VG.Proof.AesCcm.X86_64 (CtrCall)
open VG.Impl.AesSiv.X86_64 (csImm csImmF dOff dOffF)

/-- What `vg_cmac_aes_finalize`'s code computes, from any subkeys. -/
def finalizeRawX86_64 : Contract isa where
  pre := finalizeX86_64.pre
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 16 =
      Spec.Cmac.aesWith (s.gpr .rsi).toNat (Spec.Aes.bytesAt s.mem (s.gpr .rdi) (16 * ((s.gpr .rsi).toNat + 1)))
        (Spec.Cmac.xor (mn s.mem (s.gpr .rdi) (s.gpr .rcx) (s.gpr .r8).toNat)
          (Spec.Aes.bytesAt s.mem (s.gpr .rdx) 16))
  pub := finalizeX86_64.pub

theorem finalize_raw_wp (v : Ctr32Impl) {s₀ : State} (h0 : finalizeX86_64.pre s₀) :
    WP isa (Impl.CmacAes.X86_64.finalize v.callee) s₀
      fun s' => gprPreserved s₀ s' ∧ finalizeRawX86_64.post s₀ s' := by
  have hp := FPre.of h0
  have sw := FPre.scr_wrap_of h0
  generalize hW : s₀.gpr .rdi = W at hp
  generalize hSt : s₀.gpr .rdx = St at hp
  generalize hP : s₀.gpr .rcx = P at hp
  generalize s₀.gpr .r9 = S at hp sw
  generalize hL : (s₀.gpr .r8).toNat = L at hp
  generalize hR' : (s₀.gpr .rsi).toNat = R at hp
  have hR := hp.rounds
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> omega_using [h]
  refine WP.seq (WP.mono (finPre_wp hp sw) fun s₁ h₁ => ?_)
  refine WP.mono (ctrCall_ok v h₁.pre) fun s₂ h₂ => ?_
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := h₁.saved _ (by simp [calleeSaved])
  have big : Frame [⟨St, 16⟩, ⟨S, 2176⟩, below (s₀.gpr .rsp) 8] s₀.mem s₂.mem := by
    refine (h₁.frame.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨S, 2176⟩, by simp, hp.cD (by decide)⟩
      · exact ⟨⟨St, 16⟩, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨S, 2176⟩, by simp, hp.cD (by decide)⟩
      · exact ⟨⟨St, 16⟩, by simp, fun _ h => h⟩
      · exact ⟨⟨S, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨below (s₀.gpr .rsp) 8, by simp, by rw [rsp₁]; exact fun _ h => h⟩
  have sch : Spec.Aes.bytesAt s₁.mem W (16 * (R + 1)) = Spec.Aes.bytesAt s₀.mem W (16 * (R + 1)) :=
    bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.key_scr.sub_left (Region.sub_prefix (by omega_using [hR]))).sub_right (hp.cD (by decide))
      · exact hp.key_st.sub_left (Region.sub_prefix (by omega_using [hR]))) (by omega_using [hR])
  refine ⟨⟨fun r hr => by rw [h₂.saved r hr, h₁.saved r hr], ?_⟩, ?_⟩
  · refine big.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_scr
    · exact Offset.base_disjoint_below _ (by decide)
  · show Spec.Aes.bytesAt s₂.mem (s₀.gpr .rdx) 16 = _
    rw [hW, hSt, hP, hL, hR', h₂.out, sch, h₁.blk]

theorem finalize_raw_correct (v : Ctr32Impl) (s : State) (hs : finalizeRawX86_64.pre s) :
    ∃ t s', Exec isa (Impl.CmacAes.X86_64.finalize v.callee) s t s' ∧ abiPreserved s s' ∧
      finalizeRawX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := finalize_raw_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (finalize_mx v) he hg, hp⟩

/-- What a call of `vg_cmac_aes_finalize` leaves, from any subkeys. -/
structure FRPost (s : State) (K St P : Addr) (X : Region) (L R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨St, 16⟩, X, below (s.gpr .rsp) 16] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem St 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem K (16 * (R + 1)))
      (Spec.Cmac.xor (mn s.mem K P L) (Spec.Aes.bytesAt s.mem St 16))

theorem finr_call (v : Ctr32Impl) (nm : String) {s : State} {K St P S : Addr} {L R : Nat}
    (h : FArgs s K St P S L R) :
    WP isa (.call nm (Impl.CmacAes.X86_64.finalize v.callee)) s (FRPost s K St P ⟨S, 2176⟩ L R) := by
  have hR := VG.Proof.CmacAes.X86_64.toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega_using [this])
  refine WP.call (k := finalizeRawX86_64) (finalize_raw_correct v) (finalize_nosp v)
    (by rw [finalize_depth]; decide) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [finalize_depth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
  simp only [finalizeRawX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hL] at hpost
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega_using [h]
  have eK : Spec.Aes.bytesAt s.callEntry.mem K (16 * (R + 1)) = Spec.Aes.bytesAt s.mem K (16 * (R + 1)) :=
    callEntry_bytes s (h.stkK.sub_right (Region.sub_prefix (by omega_using [hRb]))) (by omega_using [hRb])
  have eK1 : Spec.Aes.bytesAt s.callEntry.mem (K + BitVec.ofNat 64 240) 16 =
      Spec.Aes.bytesAt s.mem (K + BitVec.ofNat 64 240) 16 :=
    callEntry_bytes s (h.stkK.sub_right (Offset.sub_base K (d := 240) (n := 16) (by decide))) (by decide)
  have eK2 : Spec.Aes.bytesAt s.callEntry.mem (K + BitVec.ofNat 64 256) 16 =
      Spec.Aes.bytesAt s.mem (K + BitVec.ofNat 64 256) 16 :=
    callEntry_bytes s (h.stkK.sub_right (Offset.sub_base K (d := 256) (n := 16) (by decide))) (by decide)
  have eSt := callEntry_bytes s h.stkSt (by decide)
  have eP := callEntry_bytes s h.stkP (by have := h.len; omega_using [hL])
  simp only [mn, eK, eK1, eK2, eSt, eP] at hpost
  rw [← hm₂]
  exact hpost

/-! ## `vg_cmac_aes_finalize` with any subkeys, without working space for `vg_aes_ctr32` -/

/-- `finalizeRawX86_64` when `vg_aes_ctr32` needs no working space: of
`scratch`, only the counter block at `scratch + 2048` is written. -/
def finalizeRawX86_64F : Contract isa where
  pre := finalizeX86_64F.pre
  post := finalizeRawX86_64.post
  pub := finalizeX86_64F.pub

theorem finalizeF_raw_wp (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) {s₀ : State}
    (h0 : finalizeX86_64F.pre s₀) :
    WP isa (Impl.CmacAes.X86_64.finalize v.callee) s₀
      fun s' => gprPreserved s₀ s' ∧ finalizeRawX86_64.post s₀ s' := by
  have hp := FPre.ofF h0
  generalize hW : s₀.gpr .rdi = W at hp
  generalize hSt : s₀.gpr .rdx = St at hp
  generalize hP : s₀.gpr .rcx = P at hp
  generalize s₀.gpr .r9 = S at hp
  generalize hL : (s₀.gpr .r8).toNat = L at hp
  generalize hR' : (s₀.gpr .rsi).toNat = R at hp
  have hR := hp.rounds
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> omega_using [h]
  refine WP.seq (WP.mono (finPreF_wp hp) fun s₁ h₁ => ?_)
  refine WP.mono (ctrCall_okF v f h₁.pre) fun s₂ h₂ => ?_
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := h₁.saved _ (by simp [calleeSaved])
  have big : Frame [⟨St, 16⟩, ⟨S + BitVec.ofNat 64 2048, 16⟩, below (s₀.gpr .rsp) 8] s₀.mem s₂.mem := by
    refine (h₁.frame.mono fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨St, 16⟩, by simp, fun _ h => h⟩
      · exact ⟨below (s₀.gpr .rsp) 8, by simp, by rw [rsp₁]; exact fun _ h => h⟩
  have sch : Spec.Aes.bytesAt s₁.mem W (16 * (R + 1)) = Spec.Aes.bytesAt s₀.mem W (16 * (R + 1)) :=
    bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.key_scr.sub_left (Region.sub_prefix (by omega_using [hR]))).sub_right (hp.cD (by decide))
      · exact hp.key_st.sub_left (Region.sub_prefix (by omega_using [hR]))) (by omega_using [hR])
  refine ⟨⟨fun r hr => by rw [h₂.saved r hr, h₁.saved r hr], ?_⟩, ?_⟩
  · refine big.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_scr
    · exact Offset.base_disjoint_below _ (by decide)
  · show Spec.Aes.bytesAt s₂.mem (s₀.gpr .rdx) 16 = _
    rw [hW, hSt, hP, hL, hR', h₂.out, sch, h₁.blk]

theorem finalizeF_raw_correct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) (s : State)
    (hs : finalizeRawX86_64F.pre s) :
    ∃ t s', Exec isa (Impl.CmacAes.X86_64.finalize v.callee) s t s' ∧ abiPreserved s s' ∧
      finalizeRawX86_64F.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := finalizeF_raw_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (finalize_mx v) he hg, hp⟩

theorem finr_callF (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) (nm : String) {s : State}
    {K St P S : Addr} {L R : Nat} (h : FArgsF s K St P S L R) :
    WP isa (.call nm (Impl.CmacAes.X86_64.finalize v.callee)) s
      (FRPost s K St P ⟨S + BitVec.ofNat 64 2048, 16⟩ L R) := by
  have hR := VG.Proof.CmacAes.X86_64.toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega_using [this])
  refine WP.call (k := finalizeRawX86_64F) (finalizeF_raw_correct v f) (finalize_nosp v)
    (by rw [finalize_depth]; decide) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [finalize_depth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
  simp only [finalizeRawX86_64F, finalizeRawX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hL] at hpost
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega_using [h]
  have eK : Spec.Aes.bytesAt s.callEntry.mem K (16 * (R + 1)) = Spec.Aes.bytesAt s.mem K (16 * (R + 1)) :=
    callEntry_bytes s (h.stkK.sub_right (Region.sub_prefix (by omega_using [hRb]))) (by omega_using [hRb])
  have eK1 : Spec.Aes.bytesAt s.callEntry.mem (K + BitVec.ofNat 64 240) 16 =
      Spec.Aes.bytesAt s.mem (K + BitVec.ofNat 64 240) 16 :=
    callEntry_bytes s (h.stkK.sub_right (Offset.sub_base K (d := 240) (n := 16) (by decide))) (by decide)
  have eK2 : Spec.Aes.bytesAt s.callEntry.mem (K + BitVec.ofNat 64 256) 16 =
      Spec.Aes.bytesAt s.mem (K + BitVec.ofNat 64 256) 16 :=
    callEntry_bytes s (h.stkK.sub_right (Offset.sub_base K (d := 256) (n := 16) (by decide))) (by decide)
  have eSt := callEntry_bytes s h.stkSt (by decide)
  have eP := callEntry_bytes s h.stkP (by have := h.len; omega_using [hL])
  simp only [mn, eK, eK1, eK2, eSt, eP] at hpost
  rw [← hm₂]
  exact hpost

/-! ## The layouts of the working space -/

/-- A layout of the working space `W` of `encrypt` and `decrypt`. -/
structure Lay where
  /-- What the code adds to `W` for the scratch pointer of the functions it calls. -/
  x : BitVec 32
  /-- The bytes at `W + 256` a function called may write. -/
  xn : Nat
  /-- The bytes of `W` before S2V's state `D`. -/
  n : Nat

/-- Any implementations: the functions called have the 2176 bytes at their
scratch pointer `W + 256`. -/
def Lay.soft : Lay := ⟨csImm, 2176, dOff⟩

/-- Implementations of `vg_aes_ctr32` and `vg_cmac_aes_update` that never touch
their scratch buffer: `vg_cmac_aes_finalize` writes only its counter block,
at `2048` from its scratch pointer. -/
def Lay.free : Lay := ⟨csImmF, 16, dOffF⟩

/-- The two layouts. -/
def Lay.Ok (g : Lay) : Prop := g = .soft ∨ g = .free

/-- What a call may write of the working space is within it. -/
theorem Lay.Ok.le {g : Lay} (h : g.Ok) : 256 + g.xn ≤ g.n := by
  rcases h with rfl | rfl <;> decide

theorem Lay.Ok.lt {g : Lay} (h : g.Ok) : 256 < g.n := by
  rcases h with rfl | rfl <;> decide

theorem Lay.Ok.n_le {g : Lay} (h : g.Ok) : g.n ≤ 2560 := by
  rcases h with rfl | rfl <;> decide

theorem Lay.Ok.n_lt {g : Lay} (h : g.Ok) : g.n < 2 ^ 31 := by
  rcases h with rfl | rfl <;> decide

theorem sx_soft : BitVec.signExtend 64 Lay.soft.x = BitVec.ofNat 64 256 := sx_ofNat (n := 256) (by decide)

/-- The counter block of `vg_cmac_aes_finalize`, from `Lay.free`'s scratch pointer. -/
theorem free_base (W : Addr) :
    W + BitVec.signExtend 64 Lay.free.x + BitVec.ofNat 64 2048 = W + BitVec.ofNat 64 256 := by
  rw [BitVec.add_assoc]; rfl

/-! ## The arguments of the calls, in a layout -/

/-- What a call of `vg_cmac_aes_finalize` needs: `FArgs`, with the scratch
pointer and what the call may write of the working space `W` those of the
layout. -/
structure FA (g : Lay) (s : State) (K St P W : Addr) (L R : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = St
  rcx : s.gpr .rcx = P
  r8 : s.gpr .r8 = BitVec.ofNat 64 L
  r9 : s.gpr .r9 = W + BitVec.signExtend 64 g.x
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  len : L ≤ 16
  kst : (⟨K, 272⟩ : Region).Disjoint ⟨St, 16⟩
  ks : (⟨K, 272⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, g.xn⟩
  pst : (⟨P, L⟩ : Region).Disjoint ⟨St, 16⟩
  ps : (⟨P, L⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, g.xn⟩
  sts : (⟨St, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, g.xn⟩
  stkK : (below (s.gpr .rsp) 16).Disjoint ⟨K, 272⟩
  stkP : (below (s.gpr .rsp) 16).Disjoint ⟨P, L⟩
  stkSt : (below (s.gpr .rsp) 16).Disjoint ⟨St, 16⟩
  stkS : (below (s.gpr .rsp) 16).Disjoint ⟨W + BitVec.ofNat 64 256, g.xn⟩
  wrapK : K.toNat + 272 ≤ 2 ^ 64
  wrapSt : St.toNat + 16 ≤ 2 ^ 64
  wrapP : P.toNat + L ≤ 2 ^ 64
  wrapS : (W + BitVec.ofNat 64 256).toNat + g.xn ≤ 2 ^ 64
  reads : Covers ([⟨K, 272⟩, ⟨P, L⟩] ++ [⟨St, 16⟩, ⟨W + BitVec.ofNat 64 256, g.xn⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨St, 16⟩, ⟨W + BitVec.ofNat 64 256, g.xn⟩] s.wr

theorem FA.soft {s : State} {K St P W : Addr} {L R : Nat} (h : FA .soft s K St P W L R) :
    FArgs s K St P (W + BitVec.ofNat 64 256) L R :=
  ⟨h.rdi, h.rsi, h.rdx, h.rcx, h.r8, by rw [h.r9, sx_soft], h.rounds, h.len, h.kst, h.ks, h.pst, h.ps, h.sts,
    h.stkK, h.stkP, h.stkSt, h.stkS, h.wrapK, h.wrapSt, h.wrapP, h.wrapS, h.reads, h.writes⟩

theorem FA.free {s : State} {K St P W : Addr} {L R : Nat} (h : FA .free s K St P W L R) :
    FArgsF s K St P (W + BitVec.signExtend 64 Lay.free.x) L R := by
  have e := free_base W
  refine ⟨h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.rounds, h.len, h.kst, ?_, h.pst, ?_, ?_, h.stkK, h.stkP,
    h.stkSt, ?_, h.wrapK, h.wrapSt, h.wrapP, ?_, ?_, ?_⟩ <;> rw [e]
  exacts [h.ks, h.ps, h.sts, h.stkS, h.wrapS, h.reads, h.writes]

/-- What a call of `vg_cmac_aes_update` needs: `UArgs`, in the layout. -/
structure UA (g : Lay) (s : State) (K C D W : Addr) (R n : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = C
  rcx : s.gpr .rcx = D
  r8 : s.gpr .r8 = BitVec.ofNat 64 n
  r9 : s.gpr .r9 = W + BitVec.signExtend 64 g.x
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hn : 16 * n < 2 ^ 64
  wc : (⟨K, 240⟩ : Region).Disjoint ⟨C, 16⟩
  ws : (⟨K, 240⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, g.xn⟩
  dc : (⟨D, 16 * n⟩ : Region).Disjoint ⟨C, 16⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, g.xn⟩
  cs : (⟨C, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, g.xn⟩
  stkW : (below (s.gpr .rsp) 16).Disjoint ⟨K, 240⟩
  stkD : (below (s.gpr .rsp) 16).Disjoint ⟨D, 16 * n⟩
  stkC : (below (s.gpr .rsp) 16).Disjoint ⟨C, 16⟩
  stkS : (below (s.gpr .rsp) 16).Disjoint ⟨W + BitVec.ofNat 64 256, g.xn⟩
  wrapC : C.toNat + 16 ≤ 2 ^ 64
  wrapD : D.toNat + 16 * n ≤ 2 ^ 64
  wrapS : (W + BitVec.ofNat 64 256).toNat + g.xn ≤ 2 ^ 64
  reads : Covers ([⟨K, 240⟩, ⟨D, 16 * n⟩] ++ [⟨C, 16⟩, ⟨W + BitVec.ofNat 64 256, g.xn⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨W + BitVec.ofNat 64 256, g.xn⟩] s.wr

theorem UA.soft {s : State} {K C D W : Addr} {R n : Nat} (h : UA .soft s K C D W R n) :
    UArgs s K C D (W + BitVec.ofNat 64 256) R n :=
  ⟨h.rdi, h.rsi, h.rdx, h.rcx, h.r8, by rw [h.r9, sx_soft], h.rounds, h.hn, h.wc, h.ws, h.dc, h.ds, h.cs,
    h.stkW, h.stkD, h.stkC, h.stkS, h.wrapC, h.wrapD, h.wrapS, h.reads, h.writes⟩

/-- The regions of a call but the last, which the callee is not given. -/
theorem covers_init {rs ws rs' : List Region} {X : Region} (h : Covers (rs ++ (ws ++ [X])) rs') :
    Covers (rs ++ ws) rs' :=
  (Covers.of_mem fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_append_left _ hr)).trans h

theorem UA.preF {g : Lay} {s : State} {K C D W : Addr} {R n : Nat} (h : UA g s K C D W R n) :
    updateX86_64F.pre (s.callEntry.withRegions [⟨K, 240⟩, ⟨D, 16 * n⟩] [⟨C, 16⟩]) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega_using [this])
  simp only [updateX86_64F, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hN]
  exact ⟨trivial, trivial, h.wc, h.dc, h.stkC.sub_left (ret_sub _),
    h.stkW.sub_left (stk_sub _), h.stkD.sub_left (stk_sub _),
    h.stkC.sub_left (stk_sub _), h.wrapC, h.wrapD, h.rounds⟩

/-- What a call of `vg_aes_ctr32` on one block needs: `CallPre`, in the layout. -/
structure CA (g : Lay) (s : State) (K C D W : Addr) (R : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = C
  rcx : s.gpr .rcx = D
  r8 : s.gpr .r8 = 1
  r9 : s.gpr .r9 = W + BitVec.signExtend 64 g.x
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wc : (⟨K, 240⟩ : Region).Disjoint ⟨C, 16⟩
  wd : (⟨K, 240⟩ : Region).Disjoint ⟨D, 16⟩
  ws : (⟨K, 240⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, g.xn⟩
  cd : (⟨C, 16⟩ : Region).Disjoint ⟨D, 16⟩
  cs : (⟨C, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, g.xn⟩
  ds : (⟨D, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, g.xn⟩
  stkW : (below (s.gpr .rsp) 8).Disjoint ⟨K, 240⟩
  stkC : (below (s.gpr .rsp) 8).Disjoint ⟨C, 16⟩
  stkD : (below (s.gpr .rsp) 8).Disjoint ⟨D, 16⟩
  stkS : (below (s.gpr .rsp) 8).Disjoint ⟨W + BitVec.ofNat 64 256, g.xn⟩
  wrap : D.toNat + 16 ≤ 2 ^ 64
  reads : Covers ([⟨K, 240⟩] ++ [⟨C, 16⟩, ⟨D, 16⟩, ⟨W + BitVec.ofNat 64 256, g.xn⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨D, 16⟩, ⟨W + BitVec.ofNat 64 256, g.xn⟩] s.wr
  zero : Spec.Aes.bytesAt s.mem D 16 = Spec.Cmac.zeros 16

/-- `vg_aes_ctr32`'s 2048 bytes, of the 2176 at `W + 256`. -/
theorem sub_ctr (W : Addr) : Region.Sub ⟨W + BitVec.ofNat 64 256, 2048⟩ ⟨W + BitVec.ofNat 64 256, Lay.soft.xn⟩ :=
  Region.sub_prefix (by decide)

/-- A list of regions with the last narrowed to `vg_aes_ctr32`'s 2048 bytes. -/
theorem covers_ctr {rs rs' : List Region} {W : Addr}
    (h : Covers (rs ++ [⟨W + BitVec.ofNat 64 256, Lay.soft.xn⟩]) rs') :
    Covers (rs ++ [⟨W + BitVec.ofNat 64 256, 2048⟩]) rs' :=
  (Covers.of_sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, 0, by simp, by simp⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), 0, by simp,
        (show 0 + 2048 ≤ 2176 by decide)⟩).trans h

theorem CA.soft {s : State} {K C D W : Addr} {R : Nat} (h : CA .soft s K C D W R) :
    CallPre s K C D (W + BitVec.ofNat 64 256) R :=
  ⟨h.rdi, h.rsi, h.rdx, h.rcx, h.r8, by rw [h.r9, sx_soft], h.rounds, h.wc, h.wd, h.ws.sub_right (sub_ctr W),
    h.cd, h.cs.sub_right (sub_ctr W), h.ds.sub_right (sub_ctr W), h.stkW, h.stkC, h.stkD,
    h.stkS.sub_right (sub_ctr W), h.wrap,
    covers_ctr (rs := [⟨K, 240⟩] ++ [⟨C, 16⟩, ⟨D, 16⟩]) h.reads,
    covers_ctr (rs := [⟨C, 16⟩, ⟨D, 16⟩]) h.writes, h.zero⟩

theorem CA.free {g : Lay} {s : State} {K C D W : Addr} {R : Nat} (h : CA g s K C D W R) :
    CallPreF s K C D (W + BitVec.signExtend 64 g.x) R :=
  ⟨h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.rounds, h.wc, h.wd, h.cd, h.stkW, h.stkC, h.stkD, h.wrap,
    covers_init (rs := [⟨K, 240⟩]) (ws := [⟨C, 16⟩, ⟨D, 16⟩]) h.reads,
    covers_init (rs := []) (ws := [⟨C, 16⟩, ⟨D, 16⟩]) h.writes, h.zero⟩

/-- What a call of `vg_aes_ctr32` on `n` blocks needs: `AesCcm.X86_64.CtrCall`,
in the layout. -/
structure WA (g : Lay) (s : State) (K C D W : Addr) (R n : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = C
  rcx : s.gpr .rcx = D
  r8 : s.gpr .r8 = BitVec.ofNat 64 n
  r9 : s.gpr .r9 = W + BitVec.signExtend 64 g.x
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  kc : (⟨K, 240⟩ : Region).Disjoint ⟨C, 16⟩
  kd : (⟨K, 240⟩ : Region).Disjoint ⟨D, 16 * n⟩
  ks : (⟨K, 240⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, g.xn⟩
  cd : (⟨C, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩
  cs : (⟨C, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, g.xn⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, g.xn⟩
  stkK : (below (s.gpr .rsp) 8).Disjoint ⟨K, 240⟩
  stkC : (below (s.gpr .rsp) 8).Disjoint ⟨C, 16⟩
  stkD : (below (s.gpr .rsp) 8).Disjoint ⟨D, 16 * n⟩
  stkS : (below (s.gpr .rsp) 8).Disjoint ⟨W + BitVec.ofNat 64 256, g.xn⟩
  reads : Covers ([⟨K, 240⟩] ++ [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨W + BitVec.ofNat 64 256, g.xn⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨W + BitVec.ofNat 64 256, g.xn⟩] s.wr

/-- What a call of `vg_aes_ctr32` on `n` blocks leaves, writing no more than
`X` of its working space. -/
structure WPost (s : State) (K C D : Addr) (X : Region) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨D, 16 * n⟩, X, below (s.gpr .rsp) 8] s.mem s'.mem
  out : Spec.Gcm.blocksAt s'.mem D n =
    Spec.Gcm.ctr32 (Spec.Gcm.aesWith R (Spec.Aes.bytesAt s.mem K (16 * (R + 1)))) (Spec.Gcm.blockAt s.mem C)
      (Spec.Gcm.blocksAt s.mem D n)

theorem WA.soft {s : State} {K C D W : Addr} {R n : Nat} (h : WA .soft s K C D W R n) :
    CtrCall s K C D (W + BitVec.ofNat 64 256) R n :=
  ⟨h.rdi, h.rsi, h.rdx, h.rcx, h.r8, by rw [h.r9, sx_soft], h.rounds, h.wrap, h.kc, h.kd,
    h.ks.sub_right (sub_ctr W), h.cd, h.cs.sub_right (sub_ctr W), h.ds.sub_right (sub_ctr W), h.stkK, h.stkC,
    h.stkD, h.stkS.sub_right (sub_ctr W),
    covers_ctr (rs := [⟨K, 240⟩] ++ [⟨C, 16⟩, ⟨D, 16 * n⟩]) h.reads,
    covers_ctr (rs := [⟨C, 16⟩, ⟨D, 16 * n⟩]) h.writes⟩

theorem WA.preF {g : Lay} {s : State} {K C D W : Addr} {R n : Nat} (h : WA g s K C D W R n) :
    Proof.Aes.X86_64.AesNi.ctr32X86_64F.pre (s.callEntry.withRegions [⟨K, 240⟩] [⟨C, 16⟩, ⟨D, 16 * n⟩]) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat (n := n) (by have := h.wrap; omega_using [this])
  simp only [Proof.Aes.X86_64.AesNi.ctr32X86_64F, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hn]
  exact ⟨trivial, trivial, h.kc, h.kd, h.cd, h.stkC, h.stkD, h.wrap, h.rounds⟩

/-- A call of `vg_aes_ctr32` on `n` blocks that needs no working space. -/
theorem whole_callF (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) {g : Lay} {s : State}
    {K C D W : Addr} {R n : Nat} {X : Region} (h : WA g s K C D W R n) :
    WP isa (.call v.callee.name v.callee.code) s (WPost s K C D X R n) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat (n := n) (by have := h.wrap; omega_using [this])
  refine WP.call (k := Proof.Aes.X86_64.AesNi.ctr32X86_64F) f.ok v.nosp (by rw [v.depth]; decide)
    (rd := [⟨K, 240⟩]) (wr := [⟨C, 16⟩, ⟨D, 16 * n⟩]) h.preF
    (covers_init (rs := [⟨K, 240⟩]) (ws := [⟨C, 16⟩, ⟨D, 16 * n⟩]) h.reads)
    (covers_init (rs := []) (ws := [⟨C, 16⟩, ⟨D, 16 * n⟩]) h.writes) ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [v.depth] at hf
  obtain ⟨hdata, _⟩ := hpost
  simp only [State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hn,
    hm₂] at hdata
  have fE := Proof.AesCcm.X86_64.callEntry_frame s
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with rfl | rfl | rfl <;> decide
  have eK := Proof.AesCcm.X86_64.bytesAt_frame fE (p := K) (n := 16 * (R + 1))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.stkK.sub_right (Region.sub_prefix hRb)).symm) (by omega_using [hRb])
  rw [Proof.AesCcm.X86_64.blockAt_frame fE (Proof.AesCcm.X86_64.disj_below h.stkC),
    Proof.AesCcm.X86_64.blocksAt_frame fE (Proof.AesCcm.X86_64.disj_below h.stkD)
      (by have := h.wrap; omega_using [this]), eK] at hdata
  exact ⟨hrd, hwr, hcs, (show Frame ([⟨C, 16⟩, ⟨D, 16 * n⟩] ++ [below (s.gpr .rsp) 8]) s.mem s'.mem by
    simpa using hf).mono (by simp), hdata⟩

/-! ## The calls, in a layout -/

/-- The calls of `vg_cmac_aes_finalize` (made with `c`) and of `c`, in the
layout `g`: each writes, of the working space, no more than the `g.xn` bytes
at `W + 256`, and two with the same arguments leak the same. -/
structure CCalls (c : Ctr32Impl) (g : Lay) : Prop where
  fin : ∀ (nm : String) {s : State} {K St P W : Addr} {L R : Nat}, FA g s K St P W L R →
    WP isa (.call nm (Impl.CmacAes.X86_64.finalize c.callee)) s
      (FRPost s K St P ⟨W + BitVec.ofNat 64 256, g.xn⟩ L R)
  finRel : ∀ (nm : String) {P : State → State → Prop},
    (∀ s₁ s₂, P s₁ s₂ → ∃ K St Q W : Addr, ∃ L R : Nat,
      FA g s₁ K St Q W L R ∧ FA g s₂ K St Q W L R ∧ s₁.gpr .rsp = s₂.gpr .rsp) →
    RelCT isa P (.call nm (Impl.CmacAes.X86_64.finalize c.callee)) fun _ _ => True
  ctr : ∀ {s : State} {K C D W : Addr} {R : Nat}, CA g s K C D W R →
    WP isa (.call c.callee.name c.callee.code) s (CallPostX s K C D R ⟨W + BitVec.ofNat 64 256, g.xn⟩)
  ctrRel : ∀ {P : State → State → Prop},
    (∀ s₁ s₂, P s₁ s₂ → ∃ K C D W : Addr, ∃ R : Nat,
      CA g s₁ K C D W R ∧ CA g s₂ K C D W R ∧ s₁.gpr .rsp = s₂.gpr .rsp) →
    RelCT isa P (.call c.callee.name c.callee.code) fun _ _ => True
  whole : ∀ {s : State} {K C D W : Addr} {R n : Nat}, WA g s K C D W R n →
    WP isa (.call c.callee.name c.callee.code) s (WPost s K C D ⟨W + BitVec.ofNat 64 256, g.xn⟩ R n)
  wholeRel : ∀ {P : State → State → Prop},
    (∀ s₁ s₂, P s₁ s₂ → ∃ K C D W : Addr, ∃ R n : Nat,
      WA g s₁ K C D W R n ∧ WA g s₂ K C D W R n ∧ s₁.gpr .rsp = s₂.gpr .rsp) →
    RelCT isa P (.call c.callee.name c.callee.code) fun _ _ => True

/-- `CCalls`, and the calls of `v`. -/
structure Calls (v : UpdateImpl) (g : Lay) : Prop extends CCalls v.ctr g where
  upd : ∀ {s : State} {K C D W : Addr} {R n : Nat}, UA g s K C D W R n →
    WP isa (.call v.callee.name v.callee.code) s (UPostZ s K C D ⟨W + BitVec.ofNat 64 256, g.xn⟩ R n)
  updRel : ∀ {P : State → State → Prop},
    (∀ s₁ s₂, P s₁ s₂ → ∃ K C D W : Addr, ∃ R n : Nat,
      UA g s₁ K C D W R n ∧ UA g s₂ K C D W R n ∧ s₁.gpr .rsp = s₂.gpr .rsp) →
    RelCT isa P (.call v.callee.name v.callee.code) fun _ _ => True

/-- A frame with one region widened. -/
theorem frame_ctr {a b : List Region} {W : Addr} {m m' : Mem}
    (h : Frame (a ++ ⟨W + BitVec.ofNat 64 256, 2048⟩ :: b) m m') :
    Frame (a ++ ⟨W + BitVec.ofNat 64 256, Lay.soft.xn⟩ :: b) m m' :=
  h.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨_, List.mem_append_right _ List.mem_cons_self, sub_ctr W⟩
      · exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), fun _ h => h⟩

/-- Over any implementation of `vg_aes_ctr32`. -/
theorem CCalls.soft (c : Ctr32Impl) : CCalls c .soft where
  fin nm := fun h => finr_call c nm h.soft
  finRel nm := fun h => fin_rel c nm fun a b hab =>
    let ⟨K, St, Q, _, L, R, h₁, h₂, hsp⟩ := h a b hab
    ⟨K, St, Q, _, L, R, h₁.soft, h₂.soft, hsp⟩
  ctr := fun h => WP.mono (ctr_call c h.soft) fun _ p =>
    ⟨p.rd, p.wr, p.saved, frame_ctr (a := [_, _]) (b := [_]) p.frame, p.out⟩
  ctrRel := fun h => ctr_rel c fun a b hab =>
    let ⟨K, C, D, _, R, h₁, h₂, hsp⟩ := h a b hab
    ⟨K, C, D, _, R, h₁.soft, h₂.soft, hsp⟩
  whole := fun h => WP.mono (Proof.AesCcm.X86_64.ctr_call c h.soft) fun _ p =>
    ⟨p.rd, p.wr, p.saved, frame_ctr (a := [_, _]) (b := [_]) p.frame, p.out⟩
  wholeRel := fun h => Proof.AesCcm.X86_64.ctr_rel c fun a b hab =>
    let ⟨K, C, D, _, R, n, h₁, h₂, hsp⟩ := h a b hab
    ⟨K, C, D, _, R, n, h₁.soft, h₂.soft, hsp⟩

/-- Over any implementation of `vg_cmac_aes_update`. -/
theorem Calls.soft (v : UpdateImpl) : Calls v .soft where
  toCCalls := CCalls.soft v.ctr
  upd := fun h => WP.mono (upd_call v h.soft) fun _ p => ⟨p.rd, p.wr, p.saved, p.frame, p.out⟩
  updRel := fun h => upd_rel v fun a b hab =>
    let ⟨K, C, D, _, R, n, h₁, h₂, hsp⟩ := h a b hab
    ⟨K, C, D, _, R, n, h₁.soft, h₂.soft, hsp⟩

/-- Over an implementation of `vg_aes_ctr32` that never touches its scratch
buffer: `vg_cmac_aes_finalize` writes only its counter block. -/
theorem CCalls.free (c : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free c.callee) : CCalls c .free where
  fin nm := fun {s K St P W L R} h => by
    have := finr_callF c f nm h.free
    rwa [free_base W] at this
  finRel nm := fun h => fin_relF c f nm fun a b hab =>
    let ⟨K, St, Q, _, L, R, h₁, h₂, hsp⟩ := h a b hab
    ⟨K, St, Q, _, L, R, h₁.free, h₂.free, hsp⟩
  ctr := fun h => WP.mono (ctr_callF c f h.free) fun _ p =>
    ⟨p.rd, p.wr, p.saved, p.frame.mono (by simp), p.out⟩
  ctrRel := fun h => ctr_relF c f fun a b hab =>
    let ⟨K, C, D, _, R, h₁, h₂, hsp⟩ := h a b hab
    ⟨K, C, D, _, R, h₁.free, h₂.free, hsp⟩
  whole := fun h => whole_callF c f h
  wholeRel := fun {P} h => by
    refine RelCT.callEx f.ok f.ct fun s₁ s₂ hp => ?_
    obtain ⟨K, C, D, W, R, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
    refine ⟨_, _, _, _, h₁.preF, h₂.preF, ?_,
      covers_init (rs := [⟨K, 240⟩]) (ws := [⟨C, 16⟩, ⟨D, 16 * n⟩]) h₁.reads,
      covers_init (rs := []) (ws := [⟨C, 16⟩, ⟨D, 16 * n⟩]) h₁.writes,
      covers_init (rs := [⟨K, 240⟩]) (ws := [⟨C, 16⟩, ⟨D, 16 * n⟩]) h₂.reads,
      covers_init (rs := []) (ws := [⟨C, 16⟩, ⟨D, 16 * n⟩]) h₂.writes, hsp⟩
    simp only [Proof.Aes.X86_64.AesNi.ctr32X86_64F, Proof.Aes.X86_64.AesNi.ctr32X86_64, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
      h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9]
    exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- Over implementations of `vg_cmac_aes_update` and `vg_aes_ctr32` that never
touch their scratch buffers. -/
theorem Calls.free (v : UpdateImpl) (f : UpdateFree v.callee) (fc : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) :
    Calls v .free where
  toCCalls := CCalls.free v.ctr fc
  upd := fun {s K C D W R n} h => by
    have hR := toNat_rounds h.rounds
    have hN := toNat_ofNat (n := n) (by have := h.hn; omega_using [this])
    have hd := v.depth
    refine WP.call (k := updateX86_64F) f.ok v.nosp (by omega_using [hd]) h.preF
      (covers_init (rs := [⟨K, 240⟩, ⟨D, 16 * n⟩]) (ws := [⟨C, 16⟩]) h.reads)
      (covers_init (rs := []) (ws := [⟨C, 16⟩]) h.writes) ?_
    intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
    refine ⟨hrd, hwr, hcs, ?_, ?_⟩
    · have := Frame.below_mono hf (b := 16) (by omega_using [hd]) (by decide)
      exact Frame.mono (by simpa using this) (by simp)
    · simp only [updateX86_64F, updateX86_64, State.withRegions_gpr, State.withRegions_mem,
        State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
        State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
        State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hN] at hpost
      have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega_using [h]
      rw [← hm₂, hpost, Proof.CmacAes.X86_64.ciphAt, Proof.Cmac.Stream.blocksAt_eq, Proof.Cmac.Stream.blocksAt_eq,
        callEntry_bytes s (h.stkW.sub_right (Region.sub_prefix hRb)) (by omega_using [hRb]),
        callEntry_bytes s h.stkC (by decide), callEntry_bytes s h.stkD (by have := h.hn; omega_using [this])]
  updRel := fun {P} h => by
    refine RelCT.callEx f.ok f.ct fun s₁ s₂ hp => ?_
    obtain ⟨K, C, D, W, R, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
    refine ⟨_, _, _, _, h₁.preF, h₂.preF, ?_,
      covers_init (rs := [⟨K, 240⟩, ⟨D, 16 * n⟩]) (ws := [⟨C, 16⟩]) h₁.reads,
      covers_init (rs := []) (ws := [⟨C, 16⟩]) h₁.writes,
      covers_init (rs := [⟨K, 240⟩, ⟨D, 16 * n⟩]) (ws := [⟨C, 16⟩]) h₂.reads,
      covers_init (rs := []) (ws := [⟨C, 16⟩]) h₂.writes, hsp⟩
    simp only [updateX86_64F, updateX86_64, State.withRegions_gpr, State.callEntry_rsp,
      State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
      h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, hsp]
    exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesSiv.X86_64
