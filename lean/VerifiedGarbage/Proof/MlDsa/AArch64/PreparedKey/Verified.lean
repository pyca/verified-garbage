module

public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Frame
public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.FrameTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Lay
import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.AArch64.Depth
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedSat
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedState
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedDecodeTiming
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! ### `MlDsa.AArch64.Verify.OptimizedSat`, which the modules that import this one used -/

section

/-! ### `MlDsa.AArch64.Verify.OptimizedTimingBase`, which the modules that import this one used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa

def RootPair (p : Params) (S : Nat) (I : State → State → Prop) (x y : State) : Prop :=
  VR p S I x y ∧ Sign.RootSymbolsEq x y

theorem rootPair_progress {p : Params} {S : Nat} {I J : State → State → Prop} {c : Prog isa}
    (hw : ∀σ s,vPre p S σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (RootPair p S I) c fun _ _=>True) :
    RelCT isa (RootPair p S I) c (RootPair p S J) := by
  intro x y tx ty u v hr ex ey
  obtain ⟨he,_⟩ := ht _ _ _ _ _ _ hr ex ey
  obtain ⟨⟨σ,τ,hσ,hτ,pub,ix,iy⟩,et⟩ := hr
  obtain ⟨_,u',eu,ju⟩ := hw σ x hσ ix
  obtain ⟨_,v',ev,jv⟩ := hw τ y hτ iy
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  refine ⟨he,⟨σ,τ,hσ,hτ,pub,ju,jv⟩,?_⟩
  simpa only [Sign.RootSymbolsEq,VG.AArch64.Exec.syms eu,VG.AArch64.Exec.syms ev] using et

abbrev SCx (p : Params) (S j : Nat) (cn : Bool) (r : Nat) (σ s : State) : Prop :=
  ∃h A' c0 q, SC p S σ h A' c0 q j cn r s

end VG.Proof.MlDsa.AArch64.Verify.Optimized

end

end

/-! ### `MlDsa.AArch64.Message.OptimizedVerifyRoots`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts)
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Message
open Message.Optimized (rootRegions)

theorem verify_pre_extend {p : Params} {s : State}
    (h : (verifyContract p abi 16).pre (s.withRegions
      [⟨s.gpr .x0,p.pkLen⟩,⟨s.gpr .x1,64⟩,⟨s.gpr .x2,p.sigLen⟩] s.wr))
    (hr : StaticRoots 16 s)
    (hd : s.rd=[⟨s.gpr .x0,p.pkLen⟩,⟨s.gpr .x1,64⟩,⟨s.gpr .x2,p.sigLen⟩]++rootRegions s) :
    (verifyContract p (abi.withConsts signRootConsts) 16).pre s := by
  sig_pre [verifyContract,verifySig,abi,argRegs,List.range,List.range.loop] at h
  sig_pre [verifyContract,verifySig,abi,argRegs,Abi.withConsts,
    VG.Proof.MlDsa.AArch64.Sign.signRootConsts_eq,Abi.constRegions,Abi.constsHeld,
    TableConstants.staticNttWords_length,InverseTable.expandedWords_length,stackBelow,
    List.range,List.range.loop]
  obtain ⟨sp,wr,d1,d2,d3,k1,k2,k3,k4,n1,n2,n3,n4⟩ := h
  exact ⟨sp,by rw [hd]; rfl,hr.forward.held,hr.inverse.held,hr.forward.fit,hr.forward.writable,
    hr.forward.stack,hr.inverse.fit,hr.inverse.writable,hr.inverse.stack,hr.forward.aligned,hr.inverse.aligned,by rw [hd]; rfl,
    wr,d1,d2,d3,k1,k2,k3,k4,n1,n2,n3,n4⟩

end VG.Proof.MlDsa.AArch64.Message.OptimizedVerify

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign (Ok3 StaticRoots signRootConsts)
open VG.Proof.MlDsa.AArch64.Optimized

def baseSat (p : Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 0x3200 | .x3 => 0x10000
    | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000,p.pkLen⟩,⟨0x3000,64⟩,⟨0x3200,p.sigLen⟩]
  wr := [⟨0x10000,KeyGen.scrLen p⟩]

def verifySatWith (p : Params) (m : Mem) : State :=
  { baseSat p with
    mem := m
    syms := fun name=>if name="VG_MLDSA_NTT_EXPANDED" then 1048576 else 1052480
    rd := (baseSat p).rd++[⟨1048576,3904⟩,⟨1052480,3904⟩] }

theorem verifySatWith_roots (p : Params) (hp : Ok3 p) (m : Mem)
    (hf : ∀j<488,m.readW (1048576+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD j 0)
    (hi : ∀j<488,m.readW (1052480+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD j 0) :
    StaticRoots 16 (verifySatWith p m) := by
  -- The tables' addresses as numerals first: in a term that holds `p` and `m` the kernel adds
  -- 3904 to an address, and takes its remainder by 64, in unary.
  have ef : (verifySatWith p m).syms "VG_MLDSA_NTT_EXPANDED" = 1048576 := rfl
  have ei : (verifySatWith p m).syms "VG_MLDSA_INV_FOLDED" = 1052480 := rfl
  refine ⟨⟨hf,by rw [ef]; decide,?_,?_,?_,by rw [ef]; decide⟩,
    ⟨hi,by rw [ei]; decide,?_,?_,?_,by rw [ei]; decide⟩⟩
  · apply Covers.one
    exact ⟨⟨1048576,3904⟩,by simp [verifySatWith],Region.contains_self _ _⟩
  · rcases hp with rfl|rfl|rfl
    all_goals dsimp [verifySatWith,baseSat]
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq]
    all_goals exact Region.disjoint_of_sep (by decide +kernel)
  · exact Region.disjoint_of_sep (by dsimp [verifySatWith,baseSat]; decide)
  · apply Covers.one
    exact ⟨⟨1052480,3904⟩,by simp [verifySatWith],Region.contains_self _ _⟩
  · rcases hp with rfl|rfl|rfl
    all_goals dsimp [verifySatWith,baseSat]
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq]
    all_goals exact Region.disjoint_of_sep (by decide +kernel)
  · exact Region.disjoint_of_sep (by dsimp [verifySatWith,baseSat]; decide)

theorem verifySatWith_pre (p : Params) (hp : Ok3 p) (m : Mem)
    (hf : ∀j<488,m.readW (1048576+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD j 0)
    (hi : ∀j<488,m.readW (1052480+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD j 0) :
    (verifyContract p (abi.withConsts signRootConsts) 16).pre (verifySatWith p m) := by
  apply Message.OptimizedVerify.verify_pre_extend ?_ (verifySatWith_roots p hp m hf hi) rfl
  have hb : (verifyContract p abi 16).pre (baseSat p) := by
    rcases hp with rfl|rfl|rfl
    all_goals sig_sat_check [verifyContract,verifySig,abi,argRegs,baseSat,List.range,List.range.loop]
  sig_pre [verifyContract,verifySig,abi,argRegs,List.range,List.range.loop] at hb ⊢
  exact hb

end VG.Proof.MlDsa.AArch64.Verify.Optimized

end

end

/-! # Verified preparation of canonical ML-DSA key transforms -/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.PreparedKey
open VG.Impl.MlDsa.AArch64.Call (seqR)
open VG.Spec.Sha3 (bytesAt)

theorem public_sizes {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    p.pkLen < 2 ^ 32 ∧ p.pkLen + 1024 * p.k < 2 ^ 32 := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem secret_sizes {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    p.skLen < 2 ^ 32 ∧ p.skLen + 1024 * (p.ℓ + 2 * p.k) < 2 ^ 32 := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem public_correct {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)
    (σ : State) (hpre : (preparePublicKeyContract p AArch64.abi 80).pre σ) :
    ∃ tr t, Exec isa (preparePublic p) σ tr t ∧ abiPreserved σ t ∧
      (preparePublicKeyContract p AArch64.abi 80).post σ t := by
  have sizes := public_sizes hp
  have hd : 16 * (Code.seq (copy (.x26, 0) (.x25, 0) p.pkLen)
      (seqR (publicPoly p) 0 p.k)).aarch64Depth + 64 < 2 ^ 64 := by
    rcases hp with rfl | rfl | rfl <;> decide +kernel
  have hw := prepareFrame_correct (B := PreparedPublicKey p) hd (fun s L =>
    WP.mono (public_body hp s L) fun t ⟨ht, hc⟩ =>
      ⟨ht.post, ht.x24, by rw [← ht.post.pa (p := (.x26, 0)) (by decide)]; exact ht.encoded,
        by rw [← ht.post.pa (p := (.x26, 0)) (by decide)]; exact hc⟩)
    (public_pre hpre) sizes.1 sizes.2 (fun _ _ f hk => preparedPublicKey_frame f
      (fun R hR => by
        simp only [List.mem_singleton] at hR; subst hR
        have := (public_pre hpre).so
        simp only [preparedPublicKeyBytes, n] at this ⊢
        exact (this.sub_left (below_sub (by decide) (by decide))).symm)
      (by simp only [preparedPublicKeyBytes, n]; omega_using [sizes.2]) hk)
  obtain ⟨tr, t, he, habi, hout, hc⟩ := hw
  refine ⟨tr, t, he, habi, ?_⟩
  sig_post [preparePublicKeyContract, preparePublicKeySig, AArch64.abi, VG.AArch64.argRegs]
  exact ⟨hout, hc⟩

theorem secret_correct {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)
    (σ : State) (hpre : (prepareSecretKeyContract p AArch64.abi 80).pre σ) :
    ∃ tr t, Exec isa (prepareSecret p) σ tr t ∧ abiPreserved σ t ∧
      (prepareSecretKeyContract p AArch64.abi 80).post σ t := by
  have sizes := secret_sizes hp
  have hd : 16 * (Code.seq (copy (.x26, 0) (.x25, 0) p.skLen)
      (seqR (secretPoly p) 0 (p.ℓ + 2 * p.k))).aarch64Depth + 64 < 2 ^ 64 := by
    rcases hp with rfl | rfl | rfl <;> decide +kernel
  have hw := prepareFrame_correct (B := PreparedSecretKey p) hd (fun s L =>
    WP.mono (secret_body hp s L) fun t ⟨ht, hc⟩ =>
      ⟨ht.post, ht.x24, by rw [← ht.post.pa (p := (.x26, 0)) (by decide)]; exact ht.encoded,
        by rw [← ht.post.pa (p := (.x26, 0)) (by decide)]; exact hc⟩)
    (secret_pre hpre) sizes.1 sizes.2 (fun _ _ f hk => preparedSecretKey_frame f
      (fun R hR => by
        simp only [List.mem_singleton] at hR; subst hR
        have := (secret_pre hpre).so
        simp only [preparedSecretKeyBytes, n] at this ⊢
        exact (this.sub_left (below_sub (by decide) (by decide))).symm)
      (by simp only [preparedSecretKeyBytes, n]; omega_using [sizes.2]) hk)
  obtain ⟨tr, t, he, habi, hout, hc⟩ := hw
  refine ⟨tr, t, he, habi, ?_⟩
  sig_post [prepareSecretKeyContract, prepareSecretKeySig, AArch64.abi, VG.AArch64.argRegs]
  exact ⟨hout, hc⟩

theorem public_ct {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    ConstantTime isa (preparePublicKeyContract p AArch64.abi 80).pre
      (preparePublicKeyContract p AArch64.abi 80).pub (preparePublic p) := by
  intro x y tx ty x' y' hx hy hpub ex ey
  have sizes := public_sizes hp
  have hct := prepareFrame_tr sizes.1 sizes.2 (public_body_tr hp)
  sig_pub [preparePublicKeyContract, preparePublicKeySig, AArch64.abi, VG.AArch64.argRegs] at hpub
  exact (hct _ _ _ _ _ _ ⟨public_pre hx, public_pre hy,
    hpub.2.1, hpub.2.2.1, hpub.2.2.2, hpub.1⟩ ex ey).1

theorem secret_ct {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    ConstantTime isa (prepareSecretKeyContract p AArch64.abi 80).pre
      (prepareSecretKeyContract p AArch64.abi 80).pub (prepareSecret p) := by
  intro x y tx ty x' y' hx hy hpub ex ey
  have sizes := secret_sizes hp
  have hct := prepareFrame_tr sizes.1 sizes.2 (secret_body_tr hp)
  sig_pub [prepareSecretKeyContract, prepareSecretKeySig, AArch64.abi, VG.AArch64.argRegs] at hpub
  exact (hct _ _ _ _ _ _ ⟨secret_pre hx, secret_pre hy,
    hpub.2.1, hpub.2.2.1, hpub.2.2.2, hpub.1⟩ ex ey).1

def prepSat (bytes count : Nat) : State where
  gpr r := match r with | .x0 => 0x1000 | .x1 => 0x10000 | .x2 => 0x100000 | _ => 0
  sp := 0x1000000
  mem _ := 0
  rd := [⟨0x1000, bytes⟩]
  wr := [⟨0x10000, bytes + 1024 * count⟩, ⟨0x100000, 1024⟩]

theorem public_sat {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    ∃ s, (preparePublicKeyContract p AArch64.abi 80).pre s := by
  rcases hp with rfl | rfl | rfl
  · refine ⟨prepSat mlDsa44.pkLen mlDsa44.k, ?_⟩
    sig_sat_check [preparePublicKeyContract, preparePublicKeySig, AArch64.abi, VG.AArch64.argRegs]
  · refine ⟨prepSat mlDsa65.pkLen mlDsa65.k, ?_⟩
    sig_sat_check [preparePublicKeyContract, preparePublicKeySig, AArch64.abi, VG.AArch64.argRegs]
  · refine ⟨prepSat mlDsa87.pkLen mlDsa87.k, ?_⟩
    sig_sat_check [preparePublicKeyContract, preparePublicKeySig, AArch64.abi, VG.AArch64.argRegs]

theorem secret_sat {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    ∃ s, (prepareSecretKeyContract p AArch64.abi 80).pre s := by
  rcases hp with rfl | rfl | rfl
  · refine ⟨prepSat mlDsa44.skLen (mlDsa44.ℓ + 2 * mlDsa44.k), ?_⟩
    sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, AArch64.abi, VG.AArch64.argRegs]
  · refine ⟨prepSat mlDsa65.skLen (mlDsa65.ℓ + 2 * mlDsa65.k), ?_⟩
    sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, AArch64.abi, VG.AArch64.argRegs]
  · refine ⟨prepSat mlDsa87.skLen (mlDsa87.ℓ + 2 * mlDsa87.k), ?_⟩
    sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, AArch64.abi, VG.AArch64.argRegs]

theorem preparePublic_verified (p : Params) (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    Verified AArch64.target (preparePublic p) (preparePublicKeyContract p AArch64.abi 80) :=
  ⟨public_correct hp, public_ct hp, public_sat hp⟩

theorem prepareSecret_verified (p : Params) (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    Verified AArch64.target (prepareSecret p) (prepareSecretKeyContract p AArch64.abi 80) :=
  ⟨secret_correct hp, secret_ct hp, secret_sat hp⟩

end VG.Proof.MlDsa.AArch64.PreparedKey
