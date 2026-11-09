module

public import VerifiedGarbage.Proof.MlKem.Scrubbed
public import VerifiedGarbage.Proof.MlKem.Arm.Encaps
public import VerifiedGarbage.Spec.MlKem.EncapsH
meta import VerifiedGarbage.Spec.MlKem.EncapsH
public import VerifiedGarbage.Proof.MlKem.EncapsHSat
meta import VerifiedGarbage.Proof.MlKem.EncapsHSat
public import VerifiedGarbage.Proof.MlKem.Arm.HashCT
meta import VerifiedGarbage.Proof.MlKem.Arm.Encaps
import VerifiedGarbage.Proof.MlKem.Arm.EncryptCT
meta import VerifiedGarbage.Proof.MlKem.Arm.EncryptCT
import VerifiedGarbage.Proof.MlKem.Arm.RowCT
meta import VerifiedGarbage.Proof.MlKem.Arm.RowCT
import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
meta import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.Arm.Loops
import VerifiedGarbage.Proof.MlKem.Arm.NttInv
import VerifiedGarbage.Proof.MlKem.Arm.PrfCT
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Squeeze
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.Arm.Loops
meta import VerifiedGarbage.Proof.MlKem.Arm.NttInv
meta import VerifiedGarbage.Proof.MlKem.Arm.PrfCT
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Squeeze
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.MlKem.Arm.HashCT
meta import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on 32-bit ARM: encapsulation, constant time and `Verified`

Two runs from states that agree on the public data (the pointers, the stack
pointer, `scratch` on the stack, and `ρ` of `ek`, which the contract lets the
function leak) leak the same trace (`all_ct`), phase by phase: the load of
`scratch` from the stack pointer; the blocks by the taint analysis, from the
pointers, or because they access no memory; the hashes by `hash_ct`; and
K-PKE.Encrypt by `encrypt_ct`, whose `SampleNTT`s take the seeds of the same
`ρ`. What each run is at each point comes from its correctness
(`Encaps.lean`).

All of it holds for any parameter set: the taint analyses of the blocks whose
immediates depend on it are facts of `KemLay.CallsOk`, which the parameter set
checks by evaluation. Its `outcome` is the contract's, which ML-KEM-768's
`verified` (below) and ML-KEM-1024's (`Proof/MlKem1024/Arm/`) use.
-/

@[expose] public section

namespace VG.Proof.MlKem.Arm.Encaps

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Enc
open VG.Proof.MlKem.Arm.Sample (taint_block relct_wp)

/-- A load from the stack leaks its address, the same in two runs with the
same stack pointer. -/
theorem relct_ldrSp {P : State → State → Prop} {t : Reg} {off : Nat} (hsp : ∀ a b, P a b → a.sp = b.sp) :
    RelCT isa P (.block [.ldrSp t off]) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  have tr : ∀ {s s' : State} {tr : List Leak}, execBlock isa [.ldrSp t off] s = some (s', tr) →
      tr = [Leak.addr (State.addr (s.sp + BitVec.ofNat 32 off))] := fun {s s' tr} e => by
    simp only [execBlock] at e
    split at e
    · cases e
    · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      rw [← e.2]; rfl
  rw [tr e₁, tr e₂, hsp _ _ hp]
  exact ⟨rfl, trivial⟩

/-- Two runs, from states that agree on the public data. -/
structure Two (K : KemLay) (s₁ s₂ : State) : Prop where
  hp₁ : Pre K s₁
  hp₂ : Pre K s₂
  sp : s₁.sp = s₂.sp
  r0 : s₁.gpr .r0 = s₂.gpr .r0
  r1 : s₁.gpr .r1 = s₂.gpr .r1
  r2 : s₁.gpr .r2 = s₂.gpr .r2
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  r12 : s₁.gpr .r12 = s₂.gpr .r12
  rho : ekRho K.p (EK K s₁) = ekRho K.p (EK K s₂)

section
variable {K : KemLay} {s₁ s₂ : State} (two : Two K s₁ s₂)
include two

theorem Two.layEq : lay s₂ K = lay s₁ K := by
  simp only [Encaps.lay, pScr, pEk, pKey, pCt, two.r0, two.r2, two.r3, two.sp, two.r12]

theorem Two.regs {a b : State} (ha : EnEnv K s₁ a) (hb : EnEnv K s₂ b) :
    ∀ r ∈ [Reg.r4, .r6, .r7, .r8], a.gpr r = b.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [ha.r4, hb.r4]; exact two.r0
  · rw [ha.r6, hb.r6]; exact two.r2
  · rw [ha.ctx.r7, hb.ctx.r7, two.layEq]
  · rw [ha.r8, hb.r8]; exact two.r3

theorem Two.sub' {rs : List Reg} {a b : State} (ha : EnEnv K s₁ a) (hb : EnEnv K s₂ b)
    (hs : ∀ r ∈ rs, r ∈ [Reg.r4, .r6, .r7, .r8] := by decide) : ∀ r ∈ rs, a.gpr r = b.gpr r :=
  fun r hr => two.regs ha hb r (hs r hr)

theorem Two.hashOk {ins outs : List Piece} {a b : State} (ha : EnEnv K s₁ a) (hb : EnEnv K s₂ b)
    (hi : ∀ {s₀ s : State}, Pre K s₀ → EnEnv K s₀ s → ∀ p ∈ ins, PieceOk (lay s₀ K) eidx s false p)
    (ho : ∀ {s₀ s : State}, Pre K s₀ → EnEnv K s₀ s → ∀ p ∈ outs, PieceOk (lay s₀ K) eidx s true p) :
    HashOk (lay s₁ K) eidx ins outs a ∧ HashOk (lay s₁ K) eidx ins outs b ∧ a.sp = b.sp :=
  ⟨⟨ha.ctx, hi two.hp₁ ha, ho two.hp₁ ha⟩, by rw [← two.layEq]; exact ⟨hb.ctx, hi two.hp₂ hb, ho two.hp₂ hb⟩,
    by rw [ha.sp, hb.sp, two.sp]⟩

/-- From `G(m ‖ H(ek))` on (`tail`), in both runs. -/
theorem tail_ct :
    RelCT isa (fun a b => (F4 K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oHek) 32 = H (EK K s₁)) ∧
      (F4 K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oHek) 32 = H (EK K s₂))) (tail K) fun _ _ => True := by
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  have hK := hp₁.wf
  -- `G(m ‖ H(ek))`
  refine RelCT.seq (R := fun (a b : State) =>
      (F4 K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oG) 32 = KK K s₁ ∧ bytesAt a.mem ((lay s₁ K).A 0 oSigma) 32 = RR K s₁) ∧
      (F4 K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oG) 32 = KK K s₂ ∧ bytesAt b.mem ((lay s₂ K).A 0 oSigma) 32 = RR K s₂))
    (relct_wp (hash_ct (L := lay s₁ K) (idx := eidx) VG.Proof.MlKem.rate72 (by decide) (by decide)
      (List.cons_ne_nil _ _) fun a b hab => two.hashOk (ins := [⟨.r7, oMsg, 32⟩, ⟨.r7, oHek, 32⟩])
        (outs := [⟨.r7, oG, 64⟩]) hab.1.1.1 hab.2.1.1
        (fun hp h p hp' => by
          have hK := hp.wf
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
          rcases hp' with rfl | rfl
          · exact pieceE hp h (.inr rfl) (by simp) (by edecide) (by edecide) (by edecide) (by edecide) (by edecide)
          · exact pieceE hp h (.inr rfl) (by simp) (by edecide) (by edecide) (by edecide) (by edecide) (by edecide))
        (fun hp h p hp' => by
          have hK := hp.wf
          rw [List.mem_singleton] at hp'; subst hp'
          exact pieceE hp h (.inr rfl) (fun _ => rfl) (by edecide) (by edecide) (by edecide) (by edecide) (by edecide)))
      fun a b hab => ⟨s6_ok hp₁ hab.1, s6_ok hp₂ hab.2⟩) ?_
  -- `K` into `key`
  refine RelCT.seq (R := fun (a b : State) =>
      (F4 K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 3 0) 32 = KK K s₁ ∧ bytesAt a.mem ((lay s₁ K).A 0 oSigma) 32 = RR K s₁) ∧
      (F4 K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 3 0) 32 = KK K s₂ ∧ bytesAt b.mem ((lay s₂ K).A 0 oSigma) 32 = RR K s₂))
    (relct_wp (taint_prog [.r6, .r7] (fun a b hab => two.sub' hab.1.1.1 hab.2.1.1) (by taint_decide))
      fun a b hab => ⟨s7_ok hp₁ hab.1, s7_ok hp₂ hab.2⟩) ?_
  -- K-PKE.Encrypt
  refine RelCT.seq (R := fun (a b : State) => EnEnv K s₁ a ∧ EnEnv K s₂ b)
    (relct_wp (RelCT.pointwise fun x y hxy => ?_) fun a b hab =>
      ⟨WP.mono (s8_ok hp₁ hab.1) fun _ h => h.1, WP.mono (s8_ok hp₂ hab.2) fun _ h => h.1⟩)
    (taint_block [.r7] (fun a b hab => two.sub' hab.1 hab.2) (by taint_decide))
  have ey : EncPre K (lay s₁ K) eb y := by rw [← two.layEq]; exact encPre hp₂ hxy.2.1.1 hxy.2.1.2.1
  refine encrypt_ct (encPre hp₁ hxy.1.1.1 hxy.1.1.2.1) ey ?_
  show ekRho K.p (bytesAt x.mem ((lay s₁ K).A 2 0) K.ekLen) = ekRho K.p (bytesAt y.mem ((lay s₁ K).A 2 0) K.ekLen)
  have e₂ : bytesAt y.mem ((lay s₁ K).A 2 0) K.ekLen = EK K s₂ := by rw [← two.layEq]; exact hxy.2.1.1.ek
  rw [hxy.1.1.1.ek, e₂]; exact two.rho


theorem all_ct : RelCT isa (fun a b => Loaded s₁ a ∧ Loaded s₂ b) K.encapsBody fun _ _ => True := by
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  have hK := hp₁.wf
  -- the setup
  refine RelCT.seq (R := fun (a b : State) =>
      (EnEnv K s₁ a ∧ a.gpr .r5 = pM s₁ ∧ bytesAt a.mem ((layM s₁ K).A 2 0) 32 = M K s₁) ∧
      (EnEnv K s₂ b ∧ b.gpr .r5 = pM s₂ ∧ bytesAt b.mem ((layM s₂ K).A 2 0) 32 = M K s₂))
    (relct_wp (taint_block [.r0, .r1, .r2, .r3, .r12] (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        obtain ⟨⟨a12, ar, -⟩, ⟨b12, br, -⟩⟩ := hab
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [ar _ (by decide), br _ (by decide)]; exact two.r0
        · rw [ar _ (by decide), br _ (by decide)]; exact two.r1
        · rw [ar _ (by decide), br _ (by decide)]; exact two.r2
        · rw [ar _ (by decide), br _ (by decide)]; exact two.r3
        · rw [a12, b12]; exact two.r12) (by taint_decide))
      fun a b ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5, b6⟩⟩ =>
        ⟨setup_ok hp₁ a1 a2 a3 a4 a5 a6, setup_ok hp₂ b1 b2 b3 b4 b5 b6⟩) ?_
  -- `m` copied
  refine RelCT.seq (R := fun (a b : State) =>
      (EnEnv K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oMsg) 32 = M K s₁) ∧
      (EnEnv K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oMsg) 32 = M K s₂))
    (relct_wp (taint_prog [.r5, .r7] (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hab.1.2.1, hab.2.2.1]; exact two.r1
        · exact two.regs hab.1.1 hab.2.1 .r7 (by simp)) (by taint_decide))
      fun a b hab => ⟨WP.mono (copyM_ok hp₁ hab.1.1 hab.1.2.1 hab.1.2.2) fun _ h => ⟨h.1, h.2.1⟩,
        WP.mono (copyM_ok hp₂ hab.2.1 hab.2.2.1 hab.2.2.2) fun _ h => ⟨h.1, h.2.1⟩⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => F4 K s₁ a ∧ F4 K s₂ b)
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨s4_ok hp₁ hab.1.1 hab.1.2, s4_ok hp₂ hab.2.1 hab.2.2⟩) ?_
  -- `H(ek)`
  refine RelCT.seq (R := fun (a b : State) =>
      (F4 K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oHek) 32 = H (EK K s₁)) ∧
      (F4 K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oHek) 32 = H (EK K s₂)))
    (relct_wp (hash_ct (L := lay s₁ K) (idx := eidx) VG.Proof.MlKem.rate136 (by decide) (by decide)
      (List.cons_ne_nil _ _) fun a b hab => two.hashOk (ins := [⟨.r4, 0, K.ekLen⟩]) (outs := [⟨.r7, oHek, 32⟩])
        hab.1.1 hab.2.1
        (fun hp h p hp' => by
          have hK := hp.wf
          rw [List.mem_singleton] at hp'; subst hp'
          exact pieceE hp h (.inl rfl) (by simp) enc0 hK.encEk (by dsimp only; offs) (by dsimp only; offs) (by edecide))
        (fun hp h p hp' => by
          have hK := hp.wf
          rw [List.mem_singleton] at hp'; subst hp'
          exact pieceE hp h (.inr rfl) (fun _ => rfl) (by edecide) (by edecide) (by edecide) (by edecide) (by edecide)))
      fun a b hab => ⟨s5_ok hp₁ hab.1, s5_ok hp₂ hab.2⟩) (tail_ct two)

end

/-! ## From the entry -/

/-- `K.encaps` from its entry state `s`: `scratch` loaded, then `correct`. -/
theorem entry_correct {K : KemLay} {s : State} (hp : Pre K (withR12 s (stackArg s 0)))
    (hin : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4) :
    WP isa K.encaps s (Post K (withR12 s (stackArg s 0))) :=
  WP.seq (WP.mono (ldrSp_loaded 0 (by decide) hin) fun _ hl => correct hp hl)

/-- `all_ct` from the entry states. -/
theorem entry_ct {K : KemLay} {s₁ s₂ : State} (two : Two K (withR12 s₁ (stackArg s₁ 0)) (withR12 s₂ (stackArg s₂ 0)))
    (i₁ : InRegions (s₁.rd ++ s₁.wr) (stackArgAddr s₁ 0) 4) (i₂ : InRegions (s₂.rd ++ s₂.wr) (stackArgAddr s₂ 0) 4) :
    RelCT isa (fun a b => a = s₁ ∧ b = s₂) K.encaps fun _ _ => True :=
  RelCT.seq (R := fun a b => Loaded (withR12 s₁ (stackArg s₁ 0)) a ∧ Loaded (withR12 s₂ (stackArg s₂ 0)) b)
    (relct_wp (relct_ldrSp fun a b hab => by rw [hab.1, hab.2]; exact two.sp) fun a b hab =>
      ⟨by rw [hab.1]; exact ldrSp_loaded 0 (by decide) i₁, by rw [hab.2]; exact ldrSp_loaded 0 (by decide) i₂⟩)
    (all_ct two)

theorem preserved_withR12 {s₀ s : State} {v : BitVec 32} (h : ∀ r ∈ preserved, s.gpr r = (withR12 s₀ v).gpr r) :
    ∀ r ∈ preserved, s.gpr r = s₀.gpr r := fun r hr =>
  (h r hr).trans (withR12_ne (by rintro rfl; simp [preserved] at hr))

/-! ## The outcome -/

theorem outcome {K : KemLay} (hK : K.WF) (s₀ : State) :
    Outcome (fun iters => encapsInternal K.p iters (EK K s₀) (M K s₀))
      (if okEnc K.k (ekRho K.p (EK K s₀)) K.k then 1 else 0)
      (KK K s₀, VG.Proof.MlKem.KPke.ct K.p (aEnc (ekRho K.p (EK K s₀)) (RR K s₀)) (EK K s₀) (M K s₀) (RR K s₀)) := by
  refine VG.Proof.MlKem.outcome_of_min ?_
  rw [show minIterations = 280 from rfl]
  cases hk : okEnc K.k (ekRho K.p (EK K s₀)) K.k
  · obtain ⟨i, hi, j, hj, hn⟩ := enc_none hk
    refine .inr ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.KPke.encapsInternal_eq, VG.Proof.MlKem.KPke.kpkeEncrypt_none hi hj hn]; rfl
  · refine .inl ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.KPke.encapsInternal_eq,
      VG.Proof.MlKem.KPke.kpkeEncrypt_some ⟨hK.η₁, hK.η₂⟩ (enc_some (r := RR K s₀) hk)]; rfl

theorem EK_eq (K : KemLay) (s₀ : State) : EK K s₀ = bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r0)) K.ekLen := by
  simp only [EK, Lay.A, add_ofNat_zero]; rfl

theorem M_eq (K : KemLay) (s₀ : State) : M K s₀ = bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r1)) 32 := by
  simp only [M, Lay.A, add_ofNat_zero]; rfl

/-! ## ML-KEM-768 -/

theorem pre_of {s : State} (h : (Proof.MlKem.Scrubbed.encapsBodyContract Arm.abi 8).pre s) :
    Pre kl768 (withR12 s (stackArg s 0)) ∧ InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4 := by
  sig_pre [Proof.MlKem.Scrubbed.encapsBodyContract, Spec.MlKem.encapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h0, -, h2, h3, d1, d2, d3, d4, d5, d6, d7, d8, -, d10, -, -, b1, b2, b3, b4, b5, -,
    f1, f2, f3, f4, f5⟩ := h
  exact ⟨⟨kl768_wf, kl768_calls, h0, by show _ ∈ s.rd; rw [h2]; exact .head _,
    by show _ ∈ s.rd; rw [h2]; exact .tail _ (.head _), h3, d1, d2, d3, d4, d5, d6, d7, d8, d10, b1, b2, b3, b4, b5,
    f1, f2, f3, f4, f5⟩, ⟨_, List.mem_append_left _ (by rw [h2]; exact .tail _ (.tail _ (.head _))),
      Region.contains_self _ _⟩⟩

theorem post_of {s₀ s : State} (h0 : s.gpr .r0 = if okEnc kl768.k (ekRho kl768.p (EK kl768 s₀)) kl768.k then 1 else 0)
    (hkey : bytesAt s.mem (State.addr (pKey s₀)) 32 = KK kl768 s₀)
    (hct : bytesAt s.mem (State.addr (pCt s₀)) 1088 = VG.Proof.MlKem.KPke.ct kl768.p
      (aEnc (ekRho kl768.p (EK kl768 s₀)) (RR kl768 s₀)) (EK kl768 s₀) (M kl768 s₀) (RR kl768 s₀)) :
    (Proof.MlKem.Scrubbed.encapsBodyContract Arm.abi 8).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.encapsBodyContract, Spec.MlKem.encapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  rw [setWidth_append32, h0]
  have e0 : bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r0)) 1184 = EK kl768 s₀ := (EK_eq kl768 s₀).symm
  have e1 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r2)) 32 = KK kl768 s₀ := hkey
  have e2 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r3)) 1088 = VG.Proof.MlKem.KPke.ct kl768.p
      (aEnc (ekRho kl768.p (EK kl768 s₀)) (RR kl768 s₀)) (EK kl768 s₀) (M kl768 s₀) (RR kl768 s₀) := hct
  rw [e0, ← M_eq, e1, e2]
  exact outcome kl768_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 0 else if a = 0x8001 then 0 else if a = 0x8002 then 1 else 0
  rd := [⟨0x1000, 1184⟩, ⟨0x2000, 32⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1088⟩, ⟨0x10000, 32768⟩]

theorem verified : Verified Arm.target Impl.MlKem.Arm.encaps (Proof.MlKem.Scrubbed.encapsBodyContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h0, hkey, hct⟩ := entry_correct (pre_of hs).1 (pre_of hs).2
    exact ⟨t, s', he, ⟨preserved_withR12 hpres, hsp⟩, post_of h0 hkey hct⟩
  · sig_pub [Proof.MlKem.Scrubbed.encapsBodyContract, Spec.MlKem.encapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3, hs⟩ := hpub
    have hr : ekRho kl768.p (EK kl768 s₁) = ekRho kl768.p (EK kl768 s₂) := by
      rw [EK_eq, EK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (entry_ct ⟨(pre_of h₁).1, (pre_of h₂).1, hsp, h0, h1, h2, h3, hs, hr⟩ (pre_of h₁).2 (pre_of h₂).2
      s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_sat_check [Proof.MlKem.Scrubbed.encapsBodyContract, Spec.MlKem.encapsSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]


/-! ## `encapsH` -/

/-- Two runs of `encapsH`, from entry states that agree on the public data. -/
structure TwoH (K : KemLay) (s₁ s₂ : State) : Prop where
  hq₁ : PreH K s₁
  hq₂ : PreH K s₂
  sp : s₁.sp = s₂.sp
  r0 : s₁.gpr .r0 = s₂.gpr .r0
  r1 : s₁.gpr .r1 = s₂.gpr .r1
  r2 : s₁.gpr .r2 = s₂.gpr .r2
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  ct : stackArg s₁ 0 = stackArg s₂ 0
  scr : stackArg s₁ 1 = stackArg s₂ 1
  rho : ekRho K.p (EK K (args s₁)) = ekRho K.p (EK K (args s₂))

/-- What `encaps`'s runs of their arguments are. -/
theorem TwoH.two {K : KemLay} {s₁ s₂ : State} (t : TwoH K s₁ s₂) : Two K (args s₁) (args s₂) :=
  ⟨t.hq₁.pre, t.hq₂.pre, t.sp, t.r0, t.r2, t.r3, t.ct, t.scr, t.rho⟩

theorem all_ctH {K : KemLay} {s₁ s₂ : State} (two : TwoH K s₁ s₂) :
    RelCT isa (fun a b => Loaded (withR12 s₁ (stackArg s₁ 1)) a ∧ Loaded (withR12 s₂ (stackArg s₂ 1)) b)
      K.encapsHBody fun _ _ => True := by
  have hq₁ := two.hq₁
  have hq₂ := two.hq₂
  have hp₁ := hq₁.pre
  have hp₂ := hq₂.pre
  have tw := two.two
  -- the setup
  refine RelCT.seq (R := fun (a b : State) =>
      (a.sp = s₁.sp ∧ WP isa (.block [.ldrSp .r8 0]) a (SetH K s₁)) ∧
      (b.sp = s₂.sp ∧ WP isa (.block [.ldrSp .r8 0]) b (SetH K s₂)))
    (relct_wp (taint_block [.r0, .r1, .r2, .r3, .r12] (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        obtain ⟨⟨a12, ar, -⟩, ⟨b12, br, -⟩⟩ := hab
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [ar _ (by decide), br _ (by decide)]; exact two.r0
        · rw [ar _ (by decide), br _ (by decide)]; exact two.r1
        · rw [ar _ (by decide), br _ (by decide)]; exact two.r2
        · rw [ar _ (by decide), br _ (by decide)]; exact two.r3
        · rw [a12, b12]; exact two.scr) (by taint_decide))
      fun a b ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5, b6⟩⟩ =>
        ⟨setupH_ok hq₁ a1 (fun r hr => (a2 r hr).trans (withR12_ne hr)) a3 a4 a5 a6,
          setupH_ok hq₂ b1 (fun r hr => (b2 r hr).trans (withR12_ne hr)) b3 b4 b5 b6⟩) ?_
  -- `ct` from the stack
  refine RelCT.seq (R := fun (a b : State) => SetH K s₁ a ∧ SetH K s₂ b)
    (relct_wp (relct_ldrSp fun a b hab => by rw [hab.1.1, hab.2.1]; exact two.sp) fun a b hab =>
      ⟨hab.1.2, hab.2.2⟩) ?_
  -- `h` copied
  refine RelCT.seq (R := fun (a b : State) =>
      (EnEnv K (args s₁) a ∧ a.gpr .r5 = pM (args s₁) ∧
        bytesAt a.mem ((layM (args s₁) K).A 2 0) 32 = M K (args s₁) ∧
        bytesAt a.mem ((lay (args s₁) K).A 0 oHek) 32 = H (EK K (args s₁))) ∧
      (EnEnv K (args s₂) b ∧ b.gpr .r5 = pM (args s₂) ∧
        bytesAt b.mem ((layM (args s₂) K).A 2 0) 32 = M K (args s₂) ∧
        bytesAt b.mem ((lay (args s₂) K).A 0 oHek) 32 = H (EK K (args s₂))))
    (relct_wp (taint_prog [.r9, .r7] (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hab.1.2.2.1, hab.2.2.2.1]; exact two.r1
        · exact tw.regs hab.1.1 hab.2.1 .r7 (by simp)) (by taint_decide))
      fun a b hab =>
        ⟨WP.mono (copyH_ok hq₁ hab.1.1 hab.1.2.2.1 hab.1.2.2.2.2 hab.1.2.2.2.1) fun _ h =>
          ⟨h.1, h.2.1.trans hab.1.2.1, h.2.2⟩,
        WP.mono (copyH_ok hq₂ hab.2.1 hab.2.2.2.1 hab.2.2.2.2.2 hab.2.2.2.2.1) fun _ h =>
          ⟨h.1, h.2.1.trans hab.2.2.1, h.2.2⟩⟩) ?_
  -- `m` copied
  refine RelCT.seq (R := fun (a b : State) =>
      (EnEnv K (args s₁) a ∧ bytesAt a.mem ((lay (args s₁) K).A 0 oMsg) 32 = M K (args s₁) ∧
        bytesAt a.mem ((lay (args s₁) K).A 0 oHek) 32 = H (EK K (args s₁))) ∧
      (EnEnv K (args s₂) b ∧ bytesAt b.mem ((lay (args s₂) K).A 0 oMsg) 32 = M K (args s₂) ∧
        bytesAt b.mem ((lay (args s₂) K).A 0 oHek) 32 = H (EK K (args s₂))))
    (relct_wp (taint_prog [.r5, .r7] (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hab.1.2.1, hab.2.2.1]; exact two.r2
        · exact tw.regs hab.1.1 hab.2.1 .r7 (by simp)) (by taint_decide))
      fun a b hab => ⟨copyMh_ok hp₁ hab.1.1 hab.1.2.1 hab.1.2.2.1 hab.1.2.2.2,
        copyMh_ok hp₂ hab.2.1 hab.2.2.1 hab.2.2.2.1 hab.2.2.2.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) =>
      (F4 K (args s₁) a ∧ bytesAt a.mem ((lay (args s₁) K).A 0 oHek) 32 = H (EK K (args s₁))) ∧
      (F4 K (args s₂) b ∧ bytesAt b.mem ((lay (args s₂) K).A 0 oHek) 32 = H (EK K (args s₂))))
    (relct_wp (relct_noMem rfl) fun a b hab =>
      ⟨s4h_ok hp₁ hab.1.1 hab.1.2.1 hab.1.2.2, s4h_ok hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  exact tail_ct tw

/-- `all_ctH` from the entry states. -/
theorem entryH_ct {K : KemLay} {s₁ s₂ : State} (two : TwoH K s₁ s₂) :
    RelCT isa (fun a b => a = s₁ ∧ b = s₂) K.encapsH fun _ _ => True :=
  RelCT.seq (R := fun a b => Loaded (withR12 s₁ (stackArg s₁ 1)) a ∧ Loaded (withR12 s₂ (stackArg s₂ 1)) b)
    (relct_wp (relct_ldrSp fun a b hab => by rw [hab.1, hab.2]; exact two.sp) fun a b hab =>
      ⟨by rw [hab.1]; exact ldrSp_loaded 1 (by decide) two.hq₁.argScr,
        by rw [hab.2]; exact ldrSp_loaded 1 (by decide) two.hq₂.argScr⟩)
    (all_ctH two)

/-! ## ML-KEM-768's `encapsH` -/

theorem pre_ofH {s : State} (h : (Proof.MlKem.Scrubbed.encapsHBodyContract Arm.abi 8).pre s) : PreH kl768 s := by
  sig_pre [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h0, h1, h2, h3, d1, d2, d3, -, -, dh3, d4, d5, d6, d7, d8, -, d10, -, d12, b1, bh, b2, b3, b4, b5, -,
    f1, fh, f2, f3, f4, f5, hh⟩ := h
  have hc : ∀ k ≤ 4, Region.Contains ⟨stackArgAddr s 0, 8⟩ (State.addr (s.sp + BitVec.ofNat 32 k)) 4 := by
    intro k hk
    simp only [Region.Contains, stackArgAddr, State.addr]
    bv_omega
  have ra : (⟨stackArgAddr s 0, 8⟩ : Region) ∈ s.rd ++ s.wr := by
    rw [h2]; exact List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.head _))))
  exact ⟨⟨kl768_wf, kl768_calls, h0, by show _ ∈ s.rd; rw [h2]; exact .head _,
    by show _ ∈ s.rd; rw [h2]; exact .tail _ (.tail _ (.head _)), h3, d1, d2, d3, d4, d5, d6, d7, d8, d10,
    b1, b2, b3, b4, b5, f1, f2, f3, f4, f5⟩, by rw [h2]; exact .tail _ (.head _), dh3, bh, fh,
    by rw [EK_eq]; exact hh, ⟨_, ra, hc 0 (by decide)⟩, ⟨_, ra, hc 4 (by decide)⟩,
    d12.symm.sub_left (Region.sub_prefix (by decide))⟩

/-- `post_of` for `encapsH`, whose `m` and `key` are one register later and `ct` on the stack. -/
theorem post_ofH {s₀ s : State}
    (h0 : s.gpr .r0 = if okEnc kl768.k (ekRho kl768.p (EK kl768 (args s₀))) kl768.k then 1 else 0)
    (hkey : bytesAt s.mem (State.addr (pKey (args s₀))) 32 = KK kl768 (args s₀))
    (hct : bytesAt s.mem (State.addr (pCt (args s₀))) 1088 = VG.Proof.MlKem.KPke.ct kl768.p
      (aEnc (ekRho kl768.p (EK kl768 (args s₀))) (RR kl768 (args s₀))) (EK kl768 (args s₀)) (M kl768 (args s₀))
      (RR kl768 (args s₀))) :
    (Proof.MlKem.Scrubbed.encapsHBodyContract Arm.abi 8).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]
  rw [setWidth_append32, h0]
  have e0 : bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r0)) 1184 = EK kl768 (args s₀) :=
    (EK_eq kl768 (args s₀)).symm
  have e1 : bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r2)) 32 = M kl768 (args s₀) := (M_eq kl768 (args s₀)).symm
  have e2 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r3)) 32 = KK kl768 (args s₀) := hkey
  have e3 : bytesAt s.mem (BitVec.setWidth 64 (stackArg s₀ 0)) 1088 = VG.Proof.MlKem.KPke.ct kl768.p
      (aEnc (ekRho kl768.p (EK kl768 (args s₀))) (RR kl768 (args s₀))) (EK kl768 (args s₀)) (M kl768 (args s₀))
      (RR kl768 (args s₀)) := hct
  rw [e0, e1, e2, e3]
  exact outcome kl768_wf (args s₀)

/-- A state satisfying `encapsH`'s precondition: `ct` (`0x5000`) and `scratch` (`0x10000`) on the stack,
and `H(ek)` at `h` (`hMem`). -/
def satStateH (ekLen ctLen scr : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x50 else if a = 0x8006 then 1 else VG.Proof.MlKem.hMem ekLen a
  rd := [⟨0x1000, ekLen⟩, ⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x8000, 8⟩]
  wr := [⟨0x4000, 32⟩, ⟨0x5000, ctLen⟩, ⟨0x10000, scr⟩]

theorem satStateH_mem {ekLen ctLen scr : Nat} :
    ∀ a : Addr, a.toNat < 0x2020 → (satStateH ekLen ctLen scr).mem a = VG.Proof.MlKem.hMem ekLen a := by
  intro a ha
  have n1 : a ≠ 0x8001 := by rintro rfl; exact absurd ha (by decide)
  have n6 : a ≠ 0x8006 := by rintro rfl; exact absurd ha (by decide)
  simp only [satStateH, n1, n6, ite_false]

theorem verifiedH : Verified Arm.target Impl.MlKem.Arm.encapsH (Proof.MlKem.Scrubbed.encapsHBodyContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h0, hkey, hct⟩ := entryH_correct (pre_ofH hs)
    exact ⟨t, s', he, ⟨fun r hr => (hpres r hr).trans (args_preserved s r hr), hsp⟩, post_ofH h0 hkey hct⟩
  · sig_pub [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, g0, g1, g2, g3, gc, gs⟩ := hpub
    have hr : ekRho kl768.p (EK kl768 (args s₁)) = ekRho kl768.p (EK kl768 (args s₂)) := by
      rw [EK_eq, EK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (entryH_ct ⟨pre_ofH h₁, pre_ofH h₂, hsp, g0, g1, g2, g3, gc, gs, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩
      e₁ e₂).1
  · refine ⟨satStateH 1184 1088 32768, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | (show bytesAt (satStateH 1184 1088 32768).mem (0x2000 : BitVec 64) 32 =
              VG.Spec.MlKem.H (bytesAt (satStateH 1184 1088 32768).mem (0x1000 : BitVec 64) 1184)
           exact VG.Proof.MlKem.hMem_h_of (by decide) satStateH_mem)
        | (fail_if_success show bytesAt _ _ _ = _
           decide +kernel)

end VG.Proof.MlKem.Arm.Encaps
