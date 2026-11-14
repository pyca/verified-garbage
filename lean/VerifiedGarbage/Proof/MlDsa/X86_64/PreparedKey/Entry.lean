module

public import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.Prepare
public import VerifiedGarbage.Proof.Mcdt.X86_64
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NoSp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCall
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyCall

/-!
# ML-DSA's preparation of keys on x86-64: the entries

`vg_mldsa*_prepare_verifying_key` and `vg_mldsa*_prepare_signing_key` are
`mcdtCall n c`: a call of the preparation function `c`
(`vg_mldsa*_prepare_*_key_internal`, `preparePublic` and `prepareSecret`),
inside Intel's MXCSR prologue and epilogue, so that the NTTs it calls set no
MXCSR of their own. Their contracts are `pubK0` and `secK0`, `pubK` and
`secK` with 24 more bytes of stack, for the frame of the prologue and
epilogue and the return address of the call
(`Proof.Mcdt.X86_64.mcdtEntry_correct`).
-/

-- separate module: the proofs of the entries, as `KeyGen/Entry.lean`, apart from their registrations (`Scrub.lean`)

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Verify.Prepare

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.PreparedKey
open VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Proof.Mcdt.X86_64 (EntryOf)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (len size : Nat)

/-- `PPre` with 56 bytes of stack. -/
structure PPre0 (σ : State) : Prop where
  sp : 56 ≤ (σ.gpr .rsp).toNat
  rd : σ.rd = [⟨σ.gpr .rdi, len⟩]
  wr : σ.wr = [⟨σ.gpr .rsi, size⟩, ⟨σ.gpr .rdx, 1024⟩]
  d1 : Region.Disjoint ⟨σ.gpr .rdi, len⟩ ⟨σ.gpr .rsi, size⟩
  d2 : Region.Disjoint ⟨σ.gpr .rdi, len⟩ ⟨σ.gpr .rdx, 1024⟩
  d3 : Region.Disjoint ⟨σ.gpr .rsi, size⟩ ⟨σ.gpr .rdx, 1024⟩
  r1 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rdi, len⟩
  r2 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rsi, size⟩
  r3 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rdx, 1024⟩
  k1 : (below (σ.gpr .rsp) 56).Disjoint ⟨σ.gpr .rdi, len⟩
  k2 : (below (σ.gpr .rsp) 56).Disjoint ⟨σ.gpr .rsi, size⟩
  k3 : (below (σ.gpr .rsp) 56).Disjoint ⟨σ.gpr .rdx, 1024⟩
  n1 : (σ.gpr .rdi).toNat + len ≤ 2 ^ 64
  n2 : (σ.gpr .rsi).toNat + size ≤ 2 ^ 64
  n3 : (σ.gpr .rdx).toNat + 1024 ≤ 2 ^ 64

end

section
variable {len size : Nat} {σ e : State} (hp : PPre0 len size σ) (he : EntryOf σ e)
include he

theorem pe_gpr {r : Reg} (h1 : r ≠ .rsp) (h3 : r ≠ .rax) (h4 : r ≠ .rbx) :
    (e.withRegions σ.rd σ.wr).gpr r = σ.gpr r := by
  rw [State.withRegions_gpr, he.gpr r h1 h3 h4]

theorem pe_rsp : (e.withRegions σ.rd σ.wr).gpr .rsp = σ.gpr .rsp - 24 := by
  rw [State.withRegions_gpr, he.rsp]

/-- The frame and the return address of the call are below `rsp`, apart from the buffers. -/
theorem pe_bytes {a : Addr} {n : Nat} (hd : (below (σ.gpr .rsp) 56).Disjoint ⟨a, n⟩) (hl : n ≤ 2 ^ 64) :
    bytesAt (e.withRegions σ.rd σ.wr).mem a n = bytesAt σ.mem a n := by
  rw [State.withRegions_mem]
  refine VG.Proof.MlKem.bytesAt_frame he.mem (fun r hr => ?_) hl
  rw [List.mem_singleton] at hr; subst hr
  exact (hd.sub_left (below_sub (by omega) (by omega))).symm

include hp in
theorem ppre_entry : PPre len size (e.withRegions σ.rd σ.wr) := by
  have e1 := pe_gpr he (r := .rdi) (by decide) (by decide) (by decide)
  have e2 := pe_gpr he (r := .rsi) (by decide) (by decide) (by decide)
  have e3 := pe_gpr he (r := .rdx) (by decide) (by decide) (by decide)
  have er := pe_rsp he
  have hsp := hp.sp
  have hret : Region.Sub ⟨(e.withRegions σ.rd σ.wr).gpr .rsp, 8⟩ (below (σ.gpr .rsp) 56) := by
    rw [er]; exact Proof.Mcdt.X86_64.sub_at _ (a := 24) (by omega) (by omega)
  have hbel : Region.Sub (below ((e.withRegions σ.rd σ.wr).gpr .rsp) 32) (below (σ.gpr .rsp) 56) := by
    rw [er]; exact Proof.Mcdt.X86_64.sub_below _ (a := 24) (by omega) (by omega)
  have hsp' : 32 ≤ ((e.withRegions σ.rd σ.wr).gpr .rsp).toNat := by
    rw [er, BitVec.toNat_sub]; have := (σ.gpr .rsp).isLt
    simp only [show (24 : BitVec 64).toNat = 24 from rfl]; omega
  refine ⟨hsp', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [State.withRegions_rd, State.withRegions_wr, e1, e2, e3]
  · exact hp.rd
  · exact hp.wr
  · exact hp.d1
  · exact hp.d2
  · exact hp.d3
  · exact hp.k1.sub_left hret
  · exact hp.k2.sub_left hret
  · exact hp.k3.sub_left hret
  · exact hp.k1.sub_left hbel
  · exact hp.k2.sub_left hbel
  · exact hp.k3.sub_left hbel
  · exact hp.n1
  · exact hp.n2
  · exact hp.n3

omit he in
include hp in
/-- The bytes of `prepared`, on return as the callee left them. -/
theorem pe_out {s₂ s' : State} (hm : Frame [below (σ.gpr .rsp) 16] s₂.mem s'.mem) {n : Nat} (hn : n ≤ size) :
    bytesAt s'.mem (σ.gpr .rsi) n = bytesAt s₂.mem (σ.gpr .rsi) n := by
  have := hp.n2
  refine VG.Proof.MlKem.bytesAt_frame hm (fun r hr => ?_) (by omega)
  rw [List.mem_singleton] at hr; subst hr
  exact ((hp.k2.sub_left (below_sub (by omega) (by omega))).sub_right (Region.sub_prefix hn)).symm

theorem ppub_entry {σ₂ e₂ : State} (he₂ : EntryOf σ₂ e₂) (h : PPub σ σ₂) :
    PPub (e.withRegions σ.rd σ.wr) (e₂.withRegions σ₂.rd σ₂.wr) := by
  obtain ⟨e1, e2, e3, e4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pe_gpr he (by decide) (by decide) (by decide), pe_gpr he₂ (by decide) (by decide) (by decide), e1]
  · rw [pe_gpr he (by decide) (by decide) (by decide), pe_gpr he₂ (by decide) (by decide) (by decide), e2]
  · rw [pe_gpr he (by decide) (by decide) (by decide), pe_gpr he₂ (by decide) (by decide) (by decide), e3]
  · rw [pe_rsp he, pe_rsp he₂, e4]

end

/-- The contract of `vg_mldsa*_prepare_verifying_key`: `pubK` with 56 bytes of stack. -/
def pubK0 (p : Params) : Contract isa where
  pre := PPre0 p.pkLen (preparedPublicKeyBytes p)
  post := (pubK p).post
  pub := PPub

/-- The contract of `vg_mldsa*_prepare_signing_key`: `secK` with 56 bytes of stack. -/
def secK0 (p : Params) : Contract isa where
  pre := PPre0 p.skLen (preparedSecretKeyBytes p)
  post := (secK p).post
  pub := PPub

/-! ## Never writing `rsp`, and how deep calls nest -/

theorem seqR_depth {f : Nat → Prog isa} {k : Nat} (h : ∀ i, (f i).depth ≤ k) :
    ∀ a n, (seqR f a n).depth ≤ k := by
  intro a n
  induction n generalizing a with
  | zero => simp [seqR, Code.depth]
  | succ n ih => simp only [seqR, Code.depth, Nat.max_le]; exact ⟨h a, ih (a + 1)⟩

theorem callAt_depth {nm : String} {c : Prog isa} {as : List (Reg × Arg)} (h : c.depth ≤ 3) :
    (callAt nm c as).depth ≤ 4 := by
  simp only [callAt, Code.depth]; omega

theorem prepare_depth {P : Prims} {len m : Nat} {U : Nat → Prog isa} (hn : P.ntt.depth ≤ 3)
    (hU : ∀ i, (U i).depth ≤ 4) : (prepare P len m U).depth ≤ 4 := by
  simp only [prepare, Code.depth, Nat.max_le]
  refine ⟨by omega, seqR_depth (fun i => ?_) _ _, ?_, by omega⟩
  · simp only [Code.depth, Nat.max_le]; exact ⟨hU i, callAt_depth hn⟩
  · simp [Impl.MlDsa.X86_64.Sign.copy, Code.depth]

theorem pub0_noSp : ∀ p ∈ params, (preparePublic P0 p).allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
  decide +kernel
theorem sec0_noSp : ∀ p ∈ params, (prepareSecret P0 p).allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
  decide +kernel

section
variable {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params)
include C hp

theorem preparePublic_noSp : NoSp (preparePublic P p) :=
  noSp_of ((prepare_q (noSpB_of C.ntt.nosp) (fun _ => SameQ.call (noSpB_of C.unpackT1.nosp) _)).trans (pub0_noSp p hp))

theorem prepareSecret_noSp : NoSp (prepareSecret P p) :=
  noSp_of ((prepare_q (noSpB_of C.ntt.nosp) (fun _ => SameQ.call (noSpB_of C.bitUnpack.nosp) _)).trans (sec0_noSp p hp))

omit hp in
theorem preparePublic_depth : (preparePublic P p).depth ≤ 4 :=
  prepare_depth C.ntt.depth fun _ => callAt_depth C.unpackT1.depth

omit hp in
theorem prepareSecret_depth : (prepareSecret P p).depth ≤ 4 :=
  prepare_depth C.ntt.depth fun _ => callAt_depth C.bitUnpack.depth

/-! ## The entries -/

omit C in
theorem pubK0_implies : (pubK0 p).Implies (preparePublicKeyContract p X86_64.abi 56) where
  pre s h := by
    sig_pre [preparePublicKeyContract, preparePublicKeySig, X86_64.abi, VG.X86_64.argRegs] at h
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := h
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩
  post s s' _ h := by
    sig_post [preparePublicKeyContract, preparePublicKeySig, X86_64.abi, VG.X86_64.argRegs]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [preparePublicKeyContract, preparePublicKeySig, X86_64.abi, VG.X86_64.argRegs] at h
    obtain ⟨hsp, hdi, hsi, hdx⟩ := h
    exact ⟨hdi, hsi, hdx, hsp⟩
  sat := by
    simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · sig_implies_sat [preparePublicKeyContract, preparePublicKeySig, X86_64.abi, VG.X86_64.argRegs]
        [prepSat] using prepSat mlDsa44.pkLen (preparedPublicKeyBytes mlDsa44)
    · sig_implies_sat [preparePublicKeyContract, preparePublicKeySig, X86_64.abi, VG.X86_64.argRegs]
        [prepSat] using prepSat mlDsa65.pkLen (preparedPublicKeyBytes mlDsa65)
    · sig_implies_sat [preparePublicKeyContract, preparePublicKeySig, X86_64.abi, VG.X86_64.argRegs]
        [prepSat] using prepSat mlDsa87.pkLen (preparedPublicKeyBytes mlDsa87)

omit C in
theorem secK0_implies : (secK0 p).Implies (prepareSecretKeyContract p X86_64.abi 56) where
  pre s h := by
    sig_pre [prepareSecretKeyContract, prepareSecretKeySig, X86_64.abi, VG.X86_64.argRegs] at h
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := h
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩
  post s s' _ h := by
    sig_post [prepareSecretKeyContract, prepareSecretKeySig, X86_64.abi, VG.X86_64.argRegs]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [prepareSecretKeyContract, prepareSecretKeySig, X86_64.abi, VG.X86_64.argRegs] at h
    obtain ⟨hsp, hdi, hsi, hdx⟩ := h
    exact ⟨hdi, hsi, hdx, hsp⟩
  sat := by
    simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · sig_implies_sat [prepareSecretKeyContract, prepareSecretKeySig, X86_64.abi, VG.X86_64.argRegs]
        [prepSat] using prepSat mlDsa44.skLen (preparedSecretKeyBytes mlDsa44)
    · sig_implies_sat [prepareSecretKeyContract, prepareSecretKeySig, X86_64.abi, VG.X86_64.argRegs]
        [prepSat] using prepSat mlDsa65.skLen (preparedSecretKeyBytes mlDsa65)
    · sig_implies_sat [prepareSecretKeyContract, prepareSecretKeySig, X86_64.abi, VG.X86_64.argRegs]
        [prepSat] using prepSat mlDsa87.skLen (preparedSecretKeyBytes mlDsa87)

omit C hp in
theorem prepEntry_dj {len size : Nat} {σ : State} (h : PPre0 len size σ) {k : Nat} (hk : k ≤ 4) :
    ∀ r ∈ σ.wr, (below (σ.gpr .rsp) (8 * k + 24)).Disjoint r ∧ Region.Disjoint ⟨σ.gpr .rsp, 8⟩ r := by
  intro r hr
  rw [h.wr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have := h.sp
  rcases hr with rfl | rfl
  · exact ⟨h.k2.sub_left (below_sub (by omega) (by omega)), h.r2⟩
  · exact ⟨h.k3.sub_left (below_sub (by omega) (by omega)), h.r3⟩

/-- `vg_mldsa*_prepare_verifying_key`: the preparation, inside Intel's MXCSR prologue and epilogue. -/
theorem preparePublicEntry_verified (n : String) :
    Verified X86_64.target (Impl.Mcdt.X86_64.mcdtCall n (preparePublic P p))
      (preparePublicKeyContract p X86_64.abi 56) := by
  have hd := preparePublic_depth C (p := p)
  refine Verified.of_correct (Proof.Mcdt.X86_64.mcdtEntry_correct (k := pubK p) (preparePublic_correct C hp)
      (preparePublic_noSp C hp) (fun σ h => by have := h.sp; omega) (fun σ e h he => ppre_entry h he)
      (fun σ h => prepEntry_dj h hd) (fun σ e s₂ s' h he hm hax hq => ?_))
    (Proof.Mcdt.X86_64.mcdtEntry_ct (k := pubK p) (preparePublic_correct C hp) (preparePublic_ct C hp)
      (preparePublic_noSp C hp) (fun σ h => by have := h.sp; omega) (fun σ e h he => ppre_entry h he)
      (fun σ₁ σ₂ _ _ h => (show PPub σ₁ σ₂ from h).2.2.2) (fun σ₁ σ₂ e₁ e₂ h₁ h₂ hpub he₁ he₂ => ppub_entry he₁ he₂ hpub))
    (pubK0_implies hp)
  obtain ⟨hb, hk⟩ := hq
  have hsz : p.pkLen ≤ preparedPublicKeyBytes p := by simp only [preparedPublicKeyBytes]; omega
  have hn1 := h.n1
  rw [pe_gpr he (r := .rsi) (by decide) (by decide) (by decide), pe_gpr he (r := .rdi) (by decide) (by decide) (by decide),
    pe_bytes he h.k1 (by omega)] at hb
  rw [pe_gpr he (r := .rsi) (by decide) (by decide) (by decide)] at hk
  exact ⟨(pe_out h hm hsz).trans hb, Message.preparedPk_congr (pe_out h hm (Nat.le_refl _)) hk⟩

/-- `vg_mldsa*_prepare_signing_key`: the preparation, inside Intel's MXCSR prologue and epilogue. -/
theorem prepareSecretEntry_verified (n : String) :
    Verified X86_64.target (Impl.Mcdt.X86_64.mcdtCall n (prepareSecret P p))
      (prepareSecretKeyContract p X86_64.abi 56) := by
  have hd := prepareSecret_depth C (p := p)
  refine Verified.of_correct (Proof.Mcdt.X86_64.mcdtEntry_correct (k := secK p) (prepareSecret_correct C hp)
      (prepareSecret_noSp C hp) (fun σ h => by have := h.sp; omega) (fun σ e h he => ppre_entry h he)
      (fun σ h => prepEntry_dj h hd) (fun σ e s₂ s' h he hm hax hq => ?_))
    (Proof.Mcdt.X86_64.mcdtEntry_ct (k := secK p) (prepareSecret_correct C hp) (prepareSecret_ct C hp)
      (prepareSecret_noSp C hp) (fun σ h => by have := h.sp; omega) (fun σ e h he => ppre_entry h he)
      (fun σ₁ σ₂ _ _ h => (show PPub σ₁ σ₂ from h).2.2.2) (fun σ₁ σ₂ e₁ e₂ h₁ h₂ hpub he₁ he₂ => ppub_entry he₁ he₂ hpub))
    (secK0_implies hp)
  obtain ⟨hb, hk⟩ := hq
  have hsz : p.skLen ≤ preparedSecretKeyBytes p := by simp only [preparedSecretKeyBytes]; omega
  have hn1 := h.n1
  rw [pe_gpr he (r := .rsi) (by decide) (by decide) (by decide), pe_gpr he (r := .rdi) (by decide) (by decide) (by decide),
    pe_bytes he h.k1 (by omega)] at hb
  rw [pe_gpr he (r := .rsi) (by decide) (by decide) (by decide)] at hk
  exact ⟨(pe_out h hm hsz).trans hb, Message.prepared_congr (pe_out h hm (Nat.le_refl _)) hk⟩

theorem preparePublicEntry_spSafe (n : String) :
    (Impl.Mcdt.X86_64.mcdtCall n (preparePublic P p)).all (fun i => !isa.writesSp i) = true :=
  Proof.Mcdt.X86_64.mcdtCall_spSafe (preparePublic_spSafe C hp)

theorem prepareSecretEntry_spSafe (n : String) :
    (Impl.Mcdt.X86_64.mcdtCall n (prepareSecret P p)).all (fun i => !isa.writesSp i) = true :=
  Proof.Mcdt.X86_64.mcdtCall_spSafe (prepareSecret_spSafe C hp)

end

end VG.Proof.MlDsa.X86_64.Verify.Prepare
