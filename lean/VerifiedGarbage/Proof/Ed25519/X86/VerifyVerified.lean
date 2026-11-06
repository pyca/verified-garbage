module

public import VerifiedGarbage.Proof.Ed25519.X86.VerifyDecode
import VerifiedGarbage.Proof.Ed25519.X86.VerifyScalar
import VerifiedGarbage.Proof.Ed25519.X86.VerifyFinish
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTBytes
import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTEquation
public import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTInputs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Ed25519.Group.Decode
import VerifiedGarbage.Proof.Ed25519.X86.WindowCT
import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ed25519.X86.VerifyLit
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyDecode
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyScalar
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyFinish
meta import VerifiedGarbage.Proof.Ed25519.VerifyBytes
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTBytes
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTEquation
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTInputs
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.Inline
meta import VerifiedGarbage.Proof.Ed25519.Group.Decode
meta import VerifiedGarbage.Proof.Ed25519.X86.WindowCT
meta import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTBlocks
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyLit
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Spec.Ed25519.Contract

/-! Merged from `Proof.Ed25519.X86.VerifyMain`. -/

@[expose] public section

section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem verificationScalar_num {s : State} (hp : VerifyPre s) :
    verificationScalar s = fe s.mem (arg s 1 + 32) 0 := by
  rw [verificationScalar, ← addr_zero (arg s 1 + BitVec.ofNat 32 32)]
  exact decode_words s.mem 8 (by have := hp.scalar.fit; omega_using [this])

private theorem verification_order (pk sig ch : List Byte)
    (hp : pk.length = 32) (hs : sig.length = 64) (hc : ch.length = 64) :
    Spec.Ed25519.verifyEquation pk sig ch =
      (decide (Spec.Ed25519.decodeLE (sig.drop 32) < Spec.Ed25519.L) &&
        (match Spec.Ed25519.decodePoint pk with
        | none => false
        | some a => match Spec.Ed25519.decodePoint (sig.take 32) with
          | none => false
          | some r => Spec.Ed25519.pointEqual
            (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (sig.drop 32)) Spec.Ed25519.basePoint)
            (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE ch) a)))) := by
  rw [Spec.Ed25519.verifyEquation, hp, hs, hc]
  simp only [bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ite_false]
  cases Spec.Ed25519.decodePoint pk <;> cases Spec.Ed25519.decodePoint (sig.take 32) <;>
    simp only [Bool.and_false]

theorem verifyEquation_result {s : State} (hp : VerifyPre s) :
    Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32)
      (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 64)
      (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 64) =
      (decide (verificationScalar s < Spec.Ed25519.L) && decodeResult s) := by
  have address : (arg s 1 + BitVec.ofNat 32 32).setWidth 64 = (arg s 1).setWidth 64 + BitVec.ofNat 64 32 :=
    addr_eq (by have hf := hp.signature_fit; omega_using [hf])
  rw [verification_order _ _ _
    (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]),
    signatureBytes_take, signatureBytes_drop, ← address]
  have zero (i : Nat) : arg s i + BitVec.ofNat 32 0 = arg s i := BitVec.add_zero _
  simp only [decodeResult, decodeRResult, inputPoint, equationResult, verificationScalar,
    verificationChallenge, zero]
  cases Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32) <;>
    cases Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) <;> rfl

theorem verifyBody_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s)
    (hy : s.syms = s₀.syms) :
    WP isa (.seq (.block verifyScalar) (.ite .e verifyDecode recoverInvalid)) s fun t =>
      Saved s₀ (arg s₀ 3) t ∧ t.gpr .eax = signWord
        (decide (verificationScalar s₀ < Spec.Ed25519.L) && decodeResult s₀) := by
  refine WP.seq (WP.mono_syms (verifyScalar_ok hp.scratch hp.scalar hs) fun a ⟨ha, za⟩ ya => ?_)
  rw [← verificationScalar_num hp] at za
  apply WP.ite (decide (verificationScalar s₀ < Spec.Ed25519.L)) za
  · intro hh
    refine WP.mono (verifyDecode_ok hp ha (ya.trans hy)) fun t ⟨ht, vt⟩ => ⟨ht, ?_⟩
    rw [hh, Bool.true_and]
    exact vt
  · intro hh
    refine WP.mono (recoverInvalid_ok a (arg s₀ 3)) fun t ⟨kt, rt⟩ => ?_
    exact ⟨ha.ikeep hp.scratch.fit (IKeep.of_field kt), by rw [hh, Bool.false_and]; exact rt⟩

theorem verify_correct {s : State} (h : verifyLocal.pre s) :
    WP isa verifyEquation s fun t => abiPreserved s t ∧ verifyLocal.post s t := by
  have hp := verify_pre h
  refine WP.seq (WP.mono_syms (abiSave_ok hp.scratch) fun a ha ya => ?_)
  refine WP.seq (WP.mono (verifyBody_ok hp ha ya) fun b ⟨hb, vb⟩ => ?_)
  refine WP.mono (verifyFinish_ok hp.scratch hb) fun t ⟨abi_t, vt, _⟩ => ⟨abi_t, ?_⟩
  change t.gpr .eax = _
  rw [vt, vb, verifyEquation_result hp]

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.VerifyCT`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyCTDecode`. -/
section
/-! Merged from `Proof.Ed25519.X86.DecodedThenCT`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyCTDecodeInput`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem VerifyCTFacts.inputBytes {s t : State} (h : VerifyCTFacts s t) {k : Nat} (hk : k < 2) :
    Spec.Ed25519.bytesAt s.mem ((arg s k + BitVec.ofNat 32 0).setWidth 64) 32 =
      Spec.Ed25519.bytesAt t.mem ((arg t k + BitVec.ofNat 32 0).setWidth 64) 32 := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  exacts [h.pkBytes, h.rBytes]

theorem VerifyPre.input {s : State} (hp : VerifyPre s) {k : Nat} (hk : k < 2) :
    SlicePre s 3 (arg s k + BitVec.ofNat 32 0) 32 := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  exacts [hp.pk, hp.r]

theorem VerifyCTFacts.inputA {s t : State} (h : VerifyCTFacts s t) : inputPoint s 0 = inputPoint t 0 :=
  congrArg Spec.Ed25519.decodePoint h.pkBytes

theorem VerifyCTFacts.inputR {s t : State} (h : VerifyCTFacts s t) : inputPoint s 1 = inputPoint t 1 :=
  congrArg Spec.Ed25519.decodePoint h.rBytes

theorem VerifyCTFacts.decOk {s t : State} (h : VerifyCTFacts s t) : decOk s 2 = decOk t 2 := by
  rw [decOk_two, decOk_two, h.inputA, h.inputR]

/-! ## Constant time of the decodings' loop -/

theorem VerifyCTFacts.edi {s₀ t₀ x y : State} (h : VerifyCTFacts s₀ t₀) (hx : Saved s₀ (arg s₀ 3) x)
    (hy : Saved t₀ (arg t₀ 3) y) : x.gpr .edi = y.gpr .edi :=
  hx.edi.trans ((h.args 3 (by decide)).trans hy.edi.symm)

theorem decodeStart_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) :
    RelCT isa (VerifySaved s₀ t₀) (.block decodeStart) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi, .esp]) _ (by native_taint_decide)
  intro s t hp
  apply regsTaint_agree
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.edi hp.1 hp.2
  · exact hp.1.esp.trans (h.pub.1.trans hp.2.esp.symm)

/-- After the copy of the input `k`: its number in slot 3. -/
def LoadedAt (u : State) (k : Nat) (x : State) : Prop :=
  Saved u (arg u 3) x ∧ fe x.mem (arg u 3) 96 = Spec.Ed25519.decodeLE
      (Spec.Ed25519.bytesAt u.mem ((arg u k + BitVec.ofNat 32 0).setWidth 64) 32) ∧
    wd x.mem (arg u 3) DTAB = BitVec.ofNat 32 (7680 + 128 * k)

/-- After its decoding. -/
def DecodedAt (u : State) (k : Nat) (x : State) : Prop :=
  Saved u (arg u 3) x ∧ wd x.mem (arg u 3) DTAB = BitVec.ofNat 32 (7680 + 128 * k)

theorem decodeLoad_at {u x : State} (hu : VerifyPre u) {k : Nat} (hk : k < 2) (hx : DecAt u k x) :
    WP isa (.block decodeLoad) x (LoadedAt u k) := by
  have hi := hu.input hk
  refine WP.mono (decodeLoad_ok hu hi hx.saved (hx.ptr hk)) fun t ⟨ht, wt, ft⟩ => ⟨ht, ?_, ?_⟩
  · rw [← addr_zero (arg u k + BitVec.ofNat 32 0), decode_words u.mem 8 (by have := hi.fit; omega_using [this])]
    apply num_congr
    intro j hj
    simp only [Nat.zero_add]
    exact congrArg BitVec.toNat (wt j hj)
  · rw [wd_frame1 ft hu.scratch.fit (by decide) (by decide) (Or.inr (by decide))]
    exact hx.tab

theorem pointDecode_at {u x : State} (hu : VerifyPre u) {k : Nat} (hx : LoadedAt u k x) :
    WP isa pointDecode x (DecodedAt u k) := by
  have cx := hx.1.ctx hu.scratch.fit hu.scratch.wr hu.scratch.stk
  refine WP.mono (pointDecode_ok cx) fun t ht => ?_
  refine ⟨hx.1.mulkeep hu.scratch.fit ht.1, ?_⟩
  rw [wd_frame1s cx ht.1.frame (by decide) (by decide) (Or.inr (by decide))]
  exact hx.2.2

theorem decodeLoad_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {k : Nat} (hk : k < 2) :
    RelCT isa (fun x y => DecAt s₀ k x ∧ DecAt t₀ k y) (.block decodeLoad) (fun _ _ => True) := by
  have hc : RelCT isa (fun x y => DecAt s₀ k x ∧ DecAt t₀ k y)
      (.block [.mov .esi (.mem (Impl.X25519.X86.sc DPTR))]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by native_taint_decide)
    intro x y hp
    exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h.edi hp.1.saved hp.2.saved)
  have hw (u x : State) (hu : VerifyPre u) (hx : DecAt u k x) :
      WP isa (.block [.mov .esi (.mem (Impl.X25519.X86.sc DPTR))]) x fun z =>
        z.gpr .edi = arg u 3 ∧ z.gpr .esi = arg u k :=
    loadWd_ok hu hx.saved (d := DPTR) (by decide) .esi (by decide) fun z hz ez _ _ =>
      WP.block_nil ⟨hz.edi, ez.trans (hx.ptr hk)⟩
  have hh := ctWithRuns hc (fun x y hp => ⟨hw s₀ x (verify_pre h.left) hp.1, hw t₀ y (verify_pre h.right) hp.2⟩)
  have hl : RelCT isa (fun x y => DecAt s₀ k x ∧ DecAt t₀ k y)
      (.block [.mov .esi (.mem (Impl.X25519.X86.sc DPTR))])
      (fun x y => x.gpr .edi = y.gpr .edi ∧ x.gpr .esi = y.gpr .esi) :=
    hh.mono (fun _ _ h => h) fun (x y : State) ⟨_, _, _, _, hx, hy⟩ =>
      ⟨hx.1.trans ((h.args 3 (by decide)).trans hy.1.symm), hx.2.trans ((h.args k (by omega)).trans hy.2.symm)⟩
  show RelCT isa _ (.block ([.mov .esi (.mem (Impl.X25519.X86.sc DPTR))] ++ copyWords 96 8)) _
  exact ctBlockAppend hl copyWords96_ct

theorem decodeNext1_ok {u x : State} (hu : VerifyPre u) {k : Nat} (hx : DecodedAt u k x) :
    WP isa (.block ([.mov .ecx (.reg .eax), .mov .edx (.mem (Impl.X25519.X86.sc DTAB)),
      .alu .add .edx (.reg .edi)] : List Instr)) x fun t =>
      t.gpr .edi = arg u 3 ∧ t.gpr .edx = arg u 3 + BitVec.ofNat 32 (7680 + 128 * k) := by
  refine Wp.wp_mov fun u1 h1 => ?_
  have hs1 := hx.1.upd h1
  refine loadWd_ok hu hs1 (d := DTAB) (by decide) .edx (by decide) fun u2 hs2 e2 g2 _ => ?_
  refine Wp.wp_add fun u3 h3 _ => WP.block_nil ⟨(hs2.upd h3).edi, ?_⟩
  rw [h3.gpr, e2, h1.mem, hx.2, hs2.edi, BitVec.add_comm]

theorem decodeNext_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {k : Nat} :
    RelCT isa (fun x y => DecodedAt s₀ k x ∧ DecodedAt t₀ k y) (.block decodeNext) (fun _ _ => True) := by
  rw [decodeNext_eq]
  have hc : RelCT isa (fun x y => DecodedAt s₀ k x ∧ DecodedAt t₀ k y)
      (.block ([.mov .ecx (.reg .eax), .mov .edx (.mem (Impl.X25519.X86.sc DTAB)),
        .alu .add .edx (.reg .edi)] : List Instr)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by native_taint_decide)
    intro x y hp
    exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h.edi hp.1.1 hp.2.1)
  have hh := ctWithRuns hc (fun x y hp => ⟨decodeNext1_ok (verify_pre h.left) hp.1,
    decodeNext1_ok (verify_pre h.right) hp.2⟩)
  have h1 : RelCT isa (fun x y => DecodedAt s₀ k x ∧ DecodedAt t₀ k y)
      (.block ([.mov .ecx (.reg .eax), .mov .edx (.mem (Impl.X25519.X86.sc DTAB)),
        .alu .add .edx (.reg .edi)] : List Instr))
      (fun x y => x.gpr .edi = y.gpr .edi ∧ x.gpr .edx = y.gpr .edx) :=
    hh.mono (fun _ _ h => h) fun (x y : State) ⟨_, _, _, _, hx, hy⟩ =>
      ⟨by rw [hx.1, hy.1, h.args 3 (by decide)], by rw [hx.2, hy.2, h.args 3 (by decide)]⟩
  refine ctBlockAppend h1 ?_
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi, .edx]) _ (by native_taint_decide)
  intro x y hp
  apply regsTaint_agree
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [hp.1, hp.2]

theorem decodeBody_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {k : Nat} (hk : k < 2) :
    RelCT isa (fun x y => DecAt s₀ k x ∧ DecAt t₀ k y) decodeBody (fun _ _ => True) := by
  have ps := verify_pre h.left
  have pt := verify_pre h.right
  have hb := h.inputBytes hk
  rw [decodeBody]
  refine seq_runs (decodeLoad_ct h hk) (fun x hx => decodeLoad_at ps hk hx) (fun y hy => decodeLoad_at pt hk hy) ?_
  refine seq_runs ?_ (fun x hx => pointDecode_at ps hx) (fun y hy => pointDecode_at pt hy) (decodeNext_ct h)
  refine (pointDecode_ct (arg s₀ 3) (s₀.gpr .esp) s₀.wr (Spec.Ed25519.decodeLE
    (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ k + BitVec.ofNat 32 0).setWidth 64) 32))).mono ?_ (fun _ _ h => h)
  intro x y ⟨hx, hy⟩
  have e3 := h.args 3 (by decide)
  have cy := verify_pointCTCtx h.right hy.1
  rw [← e3] at cy
  refine ⟨⟨⟨verify_pointCTCtx h.left hx.1, hx.1.esp, hx.1.wr⟩, hx.2.1⟩,
    ⟨⟨cy, hy.1.esp.trans h.pub.1.symm, hy.1.wr.trans ?_⟩, ?_⟩⟩
  · rw [h.right.2.1, h.left.2.1, e3]
  · rw [e3, hy.2.1, hb]

theorem decodeLoop_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) :
    RelCT isa (fun x y => DecAt s₀ 0 x ∧ DecAt t₀ 0 y) (.loop decodeBody .ne)
      (fun x y => DecAt s₀ 2 x ∧ DecAt t₀ 2 y) := by
  have ps := verify_pre h.left
  have pt := verify_pre h.right
  refine (VG.RelCT.loop (I := fun m x y => ∃ k, k + m = 2 ∧ k < 2 ∧ DecAt s₀ k x ∧ DecAt t₀ k y) ?_ 2).mono
    (fun x y hh => ⟨0, rfl, by decide, hh.1, hh.2⟩) (fun _ _ h => h)
  intro m
  have step (k : Nat) (hk : k < 2) := ((decodeBody_ct h hk).wp fun x y hh =>
    ⟨decodeBody_ok ps hk hh.1, decodeBody_ok pt hk hh.2⟩)
  rcases m with _ | _ | _ | m
  · exact VG.RelCT.of_false fun _ _ ⟨k, hkm, hk, _⟩ => by omega
  · refine ((step 1 (by decide)).mono (fun x y ⟨k, hkm, _, hx, hy⟩ => by
      obtain rfl : k = 1 := by omega
      exact ⟨hx, hy⟩) (fun _ _ h => h)).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨hx, zx⟩, ⟨hy, zy⟩⟩
    refine ⟨?_, fun _ => ⟨hx, hy⟩, fun he => ?_⟩
    · show x.zf.map (!·) = y.zf.map (!·); rw [zx, zy]
    · have : x.zf.map (!·) = some true := he
      rw [zx] at this; cases this
  · refine ((step 0 (by decide)).mono (fun x y ⟨k, hkm, _, hx, hy⟩ => by
      obtain rfl : k = 0 := by omega
      exact ⟨hx, hy⟩) (fun _ _ h => h)).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨hx, zx⟩, ⟨hy, zy⟩⟩
    refine ⟨?_, fun he => ?_, fun _ => ⟨1, by omega, 1, rfl, by decide, hx, hy⟩⟩
    · show x.zf.map (!·) = y.zf.map (!·); rw [zx, zy]
    · have : x.zf.map (!·) = some false := he
      rw [zx] at this; cases this
  · exact VG.RelCT.of_false fun _ _ ⟨k, hkm, hk, _⟩ => by omega

/-- The test of `DOK`. -/
theorem okTest_ok {u x : State} (hu : VerifyPre u) (hx : DecAt u 2 x) :
    WP isa (.block [.mov .eax (.mem (Impl.X25519.X86.sc DOK)), .alu .test .eax (.reg .eax)]) x fun t =>
      Saved u (arg u 3) t ∧ t.mem = x.mem ∧ t.zf.map (!·) = some (decOk u 2) :=
  loadWd_ok hu hx.saved (d := DOK) (by decide) .eax (by decide) fun b hb eb _ mb =>
    Wp.wp_test fun c hc zc => WP.block_nil ⟨⟨by rw [hc.gpr]; exact hb.edi, by rw [hc.gpr]; exact hb.esp,
      hc.rd.trans hb.rd, hc.wr.trans hb.wr, by rw [hc.mem]; exact hb.frame, by rw [hc.mem]; exact hb.saved, hb.stk⟩,
      hc.mem.trans mb, by rw [zc, eb, hx.ok, BitVec.and_self]; cases decOk u 2 <;> rfl⟩

/-- Runs keep their statics' addresses: a relational fact carries them. -/
theorem relCT_syms {P Q : State → State → Prop} {c : Prog isa} (h : RelCT isa P c Q)
    (A B : String → BitVec 32) :
    RelCT isa (fun x y => P x y ∧ x.syms = A ∧ y.syms = B) c
      (fun x y => Q x y ∧ x.syms = A ∧ y.syms = B) :=
  fun _ _ _ _ _ _ hp e₁ e₂ =>
    let ⟨ht, hq⟩ := h _ _ _ _ _ _ hp.1 e₁ e₂
    ⟨ht, hq, (VG.X86.Exec.syms e₁).trans hp.2.1, (VG.X86.Exec.syms e₂).trans hp.2.2⟩

theorem verifyDecode_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) :
    RelCT isa (fun x y => VerifySaved s₀ t₀ x y ∧ x.syms = s₀.syms ∧ y.syms = t₀.syms) verifyDecode
      (fun _ _ => True) := by
  have ps := verify_pre h.left
  have pt := verify_pre h.right
  rw [verifyDecode, decodeBoth]
  refine VG.RelCT.seq (M := isa)
    (R := fun (x y : State) => (DecAt s₀ 2 x ∧ x.syms = s₀.syms) ∧ (DecAt t₀ 2 y ∧ y.syms = t₀.syms)) ?_ ?_
  · exact (relCT_syms (seq_runs (decodeStart_ct h) (fun x hx => decodeStart_ok ps hx)
      (fun y hy => decodeStart_ok pt hy) (decodeLoop_ct h)) s₀.syms t₀.syms).mono (fun _ _ hh => hh)
      fun _ _ hh => ⟨⟨hh.1.1, hh.2.1⟩, hh.1.2, hh.2.2⟩
  have ht : RelCT isa (fun x y => (DecAt s₀ 2 x ∧ x.syms = s₀.syms) ∧ (DecAt t₀ 2 y ∧ y.syms = t₀.syms))
      (.block [.mov .eax (.mem (Impl.X25519.X86.sc DOK)), .alu .test .eax (.reg .eax)]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by native_taint_decide)
    intro x y hp
    exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h.edi hp.1.1.saved hp.2.1.saved)
  refine seq_runs ht (F₁ := fun t => ∃ x, DecAt s₀ 2 x ∧ Saved s₀ (arg s₀ 3) t ∧ t.mem = x.mem ∧
      t.zf.map (!·) = some (decOk s₀ 2) ∧ t.syms = s₀.syms)
    (F₂ := fun t => ∃ y, DecAt t₀ 2 y ∧ Saved t₀ (arg t₀ 3) t ∧ t.mem = y.mem ∧
      t.zf.map (!·) = some (decOk t₀ 2) ∧ t.syms = t₀.syms)
    (fun x hx => WP.mono_syms (okTest_ok ps hx.1) fun t ⟨a, b, c⟩ yt => ⟨x, hx.1, a, b, c, yt.trans hx.2⟩)
    (fun y hy => WP.mono_syms (okTest_ok pt hy.1) fun t ⟨a, b, c⟩ yt => ⟨y, hy.1, a, b, c, yt.trans hy.2⟩) ?_
  refine VG.RelCT.ite (M := isa) ?_ ?_ ?_
  · intro x y ⟨⟨_, _, _, _, zx, _⟩, ⟨_, _, _, _, zy, _⟩⟩
    show x.zf.map (!·) = y.zf.map (!·)
    rw [zx, zy, h.decOk]
  · cases ha : inputPoint s₀ 0 with
    | none =>
      exact VG.RelCT.of_false fun x y hh => by
        obtain ⟨⟨_, _, _, _, zx, _⟩, _⟩ := hh.1
        have e := hh.2
        change x.zf.map (!·) = some true at e
        rw [zx, decOk_two, ha] at e; cases e
    | some a =>
      cases hr : inputPoint s₀ 1 with
      | none =>
        exact VG.RelCT.of_false fun x y hh => by
          obtain ⟨⟨_, _, _, _, zx, _⟩, _⟩ := hh.1
          have e := hh.2
          change x.zf.map (!·) = some true at e
          rw [zx, decOk_two, ha, hr] at e; cases e
      | some r =>
        obtain ⟨Aa, hAa⟩ := VG.Proof.Ed25519.decodePoint_rep ha
        obtain ⟨Ra, hRa⟩ := VG.Proof.Ed25519.decodePoint_rep hr
        refine (verifyEquationPoints_ct h a r hAa hRa).mono ?_ (fun _ _ h => h)
        intro x y ⟨⟨⟨x', hx', sx, mx, _, yx⟩, ⟨y', hy', sy, my, _, yy⟩⟩, _⟩
        refine ⟨⟨sx, by rw [mx]; exact hx'.pts 0 (by decide) a ha, by rw [mx]; exact hx'.pts 1 (by decide) r hr,
            yx⟩,
          ⟨sy, by rw [my]; exact hy'.pts 0 (by decide) a (h.inputA ▸ ha),
            by rw [my]; exact hy'.pts 1 (by decide) r (h.inputR ▸ hr), yy⟩⟩
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.X86
end
end
end

/-! Merged from `Proof.Ed25519.X86.VerifyCTSetup`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def verifyEntryTaint : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 20 }

theorem verifyEntryTaint_wf {s : State} (h : verifyLocal.pre s) : VG.X86.Taint.Wf verifyEntryTaint s := by
  have hp := (verify_pre h).scratch
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (by cases h),
    fun _ h => (by cases h), fun _ => ⟨?_, ?_⟩, fun _ h => (by cases h)⟩
  · exact hp.sp_fit
  · intro r hr
    rw [h.2.1] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · intro a _ ha
      change _ + 1 ≤ 0 at ha
      omega_using [ha]
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := hp.sp_fit; omega_using [this]) hp.ret_sc hp.args_sc

theorem verifyEntryTaint_agree {s t : State} (h : VerifyCTFacts s t) : VG.X86.Taint.Agree verifyEntryTaint s t := by
  refine ⟨⟨?_, fun h => (by cases h)⟩, fun h => absurd rfl h,
    verifyEntryTaint_wf h.left, verifyEntryTaint_wf h.right,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => h.pub.1, ?_⟩
  · intro r hr
    simp only [verifyEntryTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r
    exact h.pub.1
  · intro k h4 hk
    change k < 20 at hk
    rw [show VG.X86.Taint.depth verifyEntryTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (verify_pre h.left).scratch.sp_fit h4 hk,
      VG.X86.Taint.argByte_eq (verify_pre h.right).scratch.sp_fit h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (h.args ((k - 4) / 4) (by omega_using [hk, h4]))

theorem verifyStart_ct : RelCT isa
    (fun s t => verifyLocal.pre s ∧ verifyLocal.pre t ∧ verifyLocal.pub s t)
    (.block (abiSave 3)) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) verifyEntryTaint _ (by native_taint_decide)
  exact fun _ _ h => verifyEntryTaint_agree ⟨h.1, h.2.1, h.2.2⟩

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem verifyBody_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) :
    RelCT isa (fun x y => VerifySaved s₀ t₀ x y ∧ x.syms = s₀.syms ∧ y.syms = t₀.syms)
      (.seq (.block verifyScalar) (.ite .e verifyDecode recoverInvalid)) (fun _ _ => True) := by
  have ps := verify_pre h.left
  have pt := verify_pre h.right
  have hs0 : RelCT isa (fun x y => VerifySaved s₀ t₀ x y ∧ x.syms = s₀.syms ∧ y.syms = t₀.syms)
      (.block verifyScalar) (fun _ _ => True) :=
    (verifyScalar_ct h).mono (fun _ _ hp => hp.1) (fun _ _ h => h)
  have hh := hs0.wp
    (F₁ := fun (t : State) => (Saved s₀ (arg s₀ 3) t ∧
      t.zf = some (decide (fe s₀.mem (arg s₀ 1 + 32) 0 < Spec.Ed25519.L))) ∧ t.syms = s₀.syms)
    (F₂ := fun (t : State) => (Saved t₀ (arg t₀ 3) t ∧
      t.zf = some (decide (fe t₀.mem (arg t₀ 1 + 32) 0 < Spec.Ed25519.L))) ∧ t.syms = t₀.syms)
    (fun _ _ hp =>
    ⟨WP.mono_syms (verifyScalar_ok ps.scratch ps.scalar hp.1.1) fun _ ht yt => ⟨ht, yt.trans hp.2.1⟩,
      WP.mono_syms (verifyScalar_ok pt.scratch pt.scalar hp.1.2) fun _ ht yt => ⟨ht, yt.trans hp.2.2⟩⟩)
  refine VG.RelCT.seq hh (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro s t hp
    change s.zf = t.zf
    rw [hp.2.1.1.2, hp.2.2.1.2, h.scalarFe]
  · exact (verifyDecode_ct h).mono (fun _ _ hp => ⟨⟨hp.1.2.1.1.1, hp.1.2.2.1.1⟩, hp.1.2.1.2, hp.1.2.2.2⟩)
      (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem verifyTail_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) :
    RelCT isa (fun x y => VerifySaved s₀ t₀ x y ∧ x.syms = s₀.syms ∧ y.syms = t₀.syms)
      (.seq (.seq (.block verifyScalar) (.ite .e verifyDecode recoverInvalid)) (.block verifyFinish))
      (fun _ _ => True) := by
  have hh := (verifyBody_ct h).wp (fun _ _ hp =>
    ⟨verifyBody_ok (verify_pre h.left) hp.1.1 hp.2.1, verifyBody_ok (verify_pre h.right) hp.1.2 hp.2.2⟩)
  refine VG.RelCT.seq (hh.mono (fun _ _ h => h) ?_) verifyFinish_ct
  intro s t hp
  exact hp.2.1.1.edi.trans ((h.args 3 (by decide)).trans hp.2.2.1.edi.symm)

theorem verify_ct : ConstantTime isa verifyLocal.pre verifyLocal.pub verifyEquation := by
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  have start := ctWithRuns verifyStart_ct (F₁ := fun u x => Saved u (arg u 3) x ∧ x.syms = u.syms)
    (F₂ := fun u x => Saved u (arg u 3) x ∧ x.syms = u.syms) (fun _ _ h =>
    ⟨WP.mono_syms (abiSave_ok (verify_pre h.1).scratch) fun _ ha ya => ⟨ha, ya⟩,
      WP.mono_syms (abiSave_ok (verify_pre h.2.1).scratch) fun _ ha ya => ⟨ha, ya⟩⟩)
  rw [verifyEquation]
  refine VG.RelCT.seq start ?_
  intro s t ts tt s' t' ⟨_, u, v, hp, hu, hv⟩ es et
  exact verifyTail_ct ⟨hp.1, hp.2.1, hp.2.2⟩ _ _ _ _ _ _ ⟨⟨hu.1, hv.1⟩, hu.2, hv.2⟩ es et

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.VerifyNarrow`. -/

/-! Transfer the verifier from its framed local contract to the reviewed ABI. -/
