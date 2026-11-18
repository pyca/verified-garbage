module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Front
public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
import VerifiedGarbage.Proof.Ecdsa.X86_64.Scalar
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.EcKey.Compressed.Parity
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.TCB.Code
import VerifiedGarbage.Proof.EcKey.Compressed.Encode
import VerifiedGarbage.Proof.Ecdh.X86_64.Main
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `EcKey.Compressed.X86_64.Contract`, which this module and modules that import it used -/

section

/-! # Compression's signature obligations on x86-64 -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64

def compressContract (C : Spec.Weierstrass.Curve) : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, C.len + 1⟩
    let pk : Region := ⟨s.gpr .rsi, 2 * C.len + 1⟩
    let ws : Region := ⟨s.gpr .rdx, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [pk] ∧ s.wr = [out, ws] ∧
      pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
      ret.Disjoint out ∧ ret.Disjoint ws ∧
      (s.gpr .rdi).toNat + C.len + 1 ≤ 2 ^ 64 ∧
      (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match Spec.EcKey.compressPublicKey C (Spec.EcKey.bytesAt s.mem (s.gpr .rsi) (2 * C.len + 1)) with
    | some bs => (s'.gpr .rax).setWidth 32 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) (C.len + 1) = bs
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) (C.len + 1) = List.replicate (C.len + 1) 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧
    s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx

theorem compress_implies (I : Spec.EcKey.Instance)
    (hsat : ∃ s, (I.compressPublicKeyContract abi 8).pre s) :
    (compressContract I.curve).Implies (I.compressPublicKeyContract abi 8) where
  pre := by
    sig_implies_pre [Spec.EcKey.Instance.compressPublicKeyContract,
      Spec.EcKey.Instance.compressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, compressContract]
  post := by
    intro s s' _ h
    sig_post [Spec.EcKey.Instance.compressPublicKeyContract,
      Spec.EcKey.Instance.compressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, compressContract]
    exact h
  pub := by
    sig_implies_pub [Spec.EcKey.Instance.compressPublicKeyContract,
      Spec.EcKey.Instance.compressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, compressContract]
  sat := hsat

def satState (len : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x8000 | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 2 * len + 1⟩]
  wr := [⟨0x1000, len + 1⟩, ⟨0x8000, 8192⟩]

end VG.Proof.EcKey.Compressed.X86_64

end

end

/-! ### `EcKey.Compressed.X86_64.Finish`, which only this module used -/

section

/-! # Write a compressed point or a completely cleared output -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/Tag.lean`, which only this module imported.
section

/-! # The compressed tag store -/

section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64

private theorem eaRsi (s : State) : s.ea { base := .rsi } = s.gpr .rsi := by
  simp [State.ea]

theorem tag_ok {c : Cfg} {s : State} {base : Addr} (hs : Scr s base size)
    (hy : c.sl Impl.Ecdh.X86_64.QY + 8 ≤ size)
    (hw : InRegions s.wr (s.gpr .rsi) 1) :
    WP isa (.block (Impl.EcKey.Compressed.X86_64.compressTag c)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rsi)
        ((((word s.mem base (c.sl Impl.Ecdh.X86_64.QY) &&& 1) + 2) &&& s.gpr .rcx).setWidth 8) ∧
      KeepRegs [.rdx] s s' := by
  apply WP.of_runBlock
  simp only [Impl.EcKey.Compressed.X86_64.compressTag, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, execAlu, Option.map_some, Option.bind_some, State.load64, State.store8,
    ea_sc, eaRsi, hs.rdi, ld_sc hs hy, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    ite_true, ite_false, reduceCtorEq, hw, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

end VG.Proof.EcKey.Compressed.X86_64
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass
open Spec.Weierstrass

theorem finish_eq (c : Cfg) : Impl.EcKey.Compressed.X86_64.compressFinish c =
    ([.mov .rcx (.mem (sc (c.sl FLAG)))] : List Instr) ++
    (Impl.EcKey.Compressed.X86_64.compressTag c ++
    (storeBytes c.C.len c.n .rsi 1 (c.sl E) ++
    (([.mov .rax (.reg .rcx), .alu .and .rax (.imm 1)] : List Instr) ++ Spill.restoreCode .rdi Cfg.saved))) := by
  simp only [Impl.EcKey.Compressed.X86_64.compressFinish, List.append_assoc]
  rfl

theorem finish_ok {c : Cfg} (hc : BaseCfgOk c) {base out : Addr} {s : State}
    (hs : Scr s base size) (hrsi : s.gpr .rsi = out)
    (hw : (⟨out, c.C.len + 1⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, c.C.len + 1⟩ ⟨base, size⟩)
    (hfit : out.toNat + c.C.len + 1 ≤ 2 ^ 64)
    {g : Reg → BitVec 64} (hsv : Spill.Saved s.mem base g Cfg.saved) (b : Bool)
    (hf : word s.mem base (c.sl FLAG) = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block (Impl.EcKey.Compressed.X86_64.compressFinish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem out (c.C.len + 1) =
        (if b then BitVec.ofNat 8 (2 + sv c base s Impl.Ecdh.X86_64.QY % 2) ::
          toBytes c.C.len (sv c base s E) else List.replicate (c.C.len + 1) 0) ∧
      (s'.gpr .rax).setWidth 32 = (if b then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) := by
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  obtain hE := sl_le c hc.n10 (i := E) (by decide)
  obtain hY := sl_le c hc.n10 (i := Impl.Ecdh.X86_64.QY) (by decide)
  obtain hF := sl_le c hc.n10 (i := FLAG) (by decide)
  have := hc.n0; have := hc.len8; have := hc.len_lo; have := hc.len_hi
  obtain htagd : Region.Disjoint ⟨base, size⟩ ⟨out, 1⟩ :=
    hd.symm.sub_right (by simpa using Offset.sub_base out (d := 0) (n := 1) (by omega_using [] : 0 + 1 ≤ c.C.len + 1))
  obtain hxd : Region.Disjoint ⟨base, size⟩ ⟨out + 1, c.C.len⟩ := by
    exact hd.symm.sub_right (Offset.sub_base out (d := 1) (by omega_using []))
  rw [finish_eq, WP.block_append_iff]
  refine WP.mono (movRcx_mem_ok hs (d := c.sl FLAG) (by omega_arith)) fun s₁ ⟨e₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  obtain hrsi₁ : s₁.gpr .rsi = out := (k₁.1 _ (by decide)).trans hrsi
  rw [WP.block_append_iff]
  refine WP.mono (tag_ok (c := c) hs₁ (by omega_arith) (by
    rw [hrsi₁, k₁.2.2.2]
    exact ⟨_, hw, by
      simpa using Offset.contains_base out (d := 0) (n := 1)
        (by omega_using [] : 0 + 1 ≤ c.C.len + 1) (by decide)⟩)) fun s₂ ⟨m₂, k₂⟩ => ?_
  rw [hrsi₁, e₁, k₁.2.1, hf, tag_byte _ _ _ _ hc.n0 b] at m₂
  obtain O₂ : Outside out 0 1 s₁.mem s₂.mem := by
    rw [m₂, k₁.2.1]
    simpa only [off, BitVec.add_zero] using
      writeW8_outside s.mem out (d := 0)
        (if b then BitVec.ofNat 8 (2 + sv c base s Impl.Ecdh.X86_64.QY % 2) else 0) (by decide)
  obtain U₂ := O₂.unch_far htagd
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  obtain hrsi₂ : s₂.gpr .rsi = out := (k₂.gpr _ (by decide)).trans hrsi₁
  obtain hrcx₂ : s₂.gpr .rcx = if b then BitVec.allOnes 64 else 0 := by
    rw [k₂.gpr _ (by decide), e₁, hf]
  obtain x₂ : wordsVal s₂.mem base (c.sl E) c.n = sv c base s E := by
    rw [U₂.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega_using [hE]) (by omega_using [hn, hE]),
      k₁.2.1]
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok hs₂ (dst := .rsi) (d := 1) (a := c.sl E) (by decide) (by decide) b
    hrcx₂ hE (by omega_arith) hc.len_lo hc.len_hi (by
      rw [hrsi₂, Offset.toNat_add_ofNat]
      simp only [show (1 : Nat) % 2 ^ 64 = 1 from rfl]
      rw [Nat.mod_eq_of_lt (by omega_arith)]
      omega_using [hfit])
    (by
      rw [hrsi₂]
      intro e m hem
      exact ⟨_, by rw [k₂.wr, k₁.2.2.2]; exact hw, by
        rw [Offset.add_add]
        exact Offset.contains_base out (by omega_using [hem]) (by omega_using [hsz, hE, this, hem])⟩)
    (by
      rw [hrsi₂]
      exact hxd.sub_left (Offset.sub_base base hE))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hrsi₂] at e₃ O₃
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  obtain U₃ := O₃.unch_far hxd
  obtain hrcx₃ : s₃.gpr .rcx = if b then BitVec.allOnes 64 else 0 :=
    (k₃.gpr _ (by decide)).trans hrcx₂
  obtain lead : s₃.mem out = if b then BitVec.ofNat 8 (2 + sv c base s Impl.Ecdh.X86_64.QY % 2) else 0 := by
    obtain hb : Spec.Ecdsa.bytesAt s₃.mem out 1 = Spec.Ecdsa.bytesAt s₂.mem out 1 :=
      bytesAt_keep O₃ (Offset.base_disjoint out (e := 1) (n := c.C.len) (k := 1)
        (by omega_using []) (by omega_using [hfit])) (by omega_using [hfit]) (by decide)
    obtain he : s₃.mem out = s₂.mem out := by simpa [Spec.Ecdsa.bytesAt] using hb
    rw [he, m₂, writeW8_self]
  rw [WP.block_append_iff]
  refine WP.mono (raxBit_ok s₃) fun s₄ ⟨e₄, k₄⟩ => ?_
  obtain hs₄ := hs₃.of_keeps k₄ (by decide)
  obtain hsv₄ : Spill.Saved s₄.mem base g Cfg.saved := by
    rw [k₄.2.1]
    obtain h48 : ∀ w ∈ [(size, 2 ^ 64)], 48 ≤ w.1 := by
      intro w hw
      simp only [List.mem_singleton] at hw
      subst w
      decide
    exact Saved.unch (Saved.unch (k₁.2.1 ▸ hsv) h48 U₂) h48 U₃
  refine WP.mono (Spill.restore_ok .rdi Cfg.saved g s₄ (by decide) (fun p hp => ?_)
    (by rw [hs₄.rdi]; exact hsv₄)) fun s₅ ⟨g₅, r₅, m₅, _, _⟩ => ?_
  · have := saved_lt p hp
    rw [hs₄.rdi]
    exact ⟨_, List.mem_append_right _ hs₄.wr, hs₄.contains (by omega_using [hsz, this]) (by decide)⟩
  refine ⟨?_, ?_, g₅⟩
  · rw [m₅, k₄.2.1, show c.C.len + 1 = 1 + c.C.len by omega_using [], bytesAt_add, e₃, x₂]
    obtain hb : Spec.Ecdsa.bytesAt s₃.mem out 1 = [s₃.mem out] := by simp [Spec.Ecdsa.bytesAt]
    rw [hb, lead]
    cases b <;> simp [Nat.add_comm, List.replicate_succ]
  · rw [r₅ _ (by decide), e₄, hrcx₃, mask_bit]

end VG.Proof.EcKey.Compressed.X86_64

end

end


/-! # Compression meets the merged API contract -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont.X86_64 VG.Proof.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdh.X86_64 Spec.Weierstrass

theorem compress_key (c : Cfg) (s : State) :
    Spec.EcKey.compressPublicKey c.C
      (Spec.EcKey.bytesAt s.mem (s.gpr .rsi) (2 * c.C.len + 1)) =
    if KeyOk c s then some (BitVec.ofNat 8 (2 + keyY c s % 2) :: toBytes c.C.len (keyX c s)) else none := by
  obtain hlen : (Spec.Ecdsa.bytesAt s.mem (s.gpr .rsi) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]
    omega_using []
  obtain hhead : (Spec.Ecdsa.bytesAt s.mem (s.gpr .rsi) (1 + 2 * c.C.len)).head? =
      some (s.mem (s.gpr .rsi)) := by rw [peer_bytes]; rfl
  obtain hx : ofBytes (((Spec.Ecdsa.bytesAt s.mem (s.gpr .rsi) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      keyX c s := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
    rfl
  obtain hy : ofBytes ((Spec.Ecdsa.bytesAt s.mem (s.gpr .rsi) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      keyY c s := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  obtain hv : Proof.Ecdh.Valid c.C (s.mem (s.gpr .rsi)) (keyX c s) (keyY c s) ↔ KeyOk c s := by
    constructor
    · rintro ⟨h4, hx, hy, he⟩
      exact ⟨⟨⟨h4, hx⟩, hy⟩, he⟩
    · rintro ⟨⟨⟨h4, hx⟩, hy⟩, he⟩
      exact ⟨h4, hx, hy, he⟩
  change Spec.EcKey.compressPublicKey c.C
    (Spec.Ecdsa.bytesAt s.mem (s.gpr .rsi) (2 * c.C.len + 1)) = _
  rw [show 2 * c.C.len + 1 = 1 + 2 * c.C.len by omega_using [], compress_eq hlen hhead hx hy]
  simp only [hv]

theorem compress_correct (c : Cfg) (hc : BaseCfgOk c)
    (hi : (Impl.EcKey.Compressed.X86_64.compress c).InlineOk = true)
    (hmx : (Impl.EcKey.Compressed.X86_64.compress c).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (hs : (compressContract c.C).pre s) :
    ∃ t s', Exec isa (Impl.EcKey.Compressed.X86_64.compress c).inline s t s' ∧
      abiPreserved s s' ∧ (compressContract c.C).post s s' := by
  obtain ⟨hrd, hwr, hpo, hpw, how, hro, hrw, hfit, hwfit⟩ := hs
  obtain hp : Pre c s :=
    ⟨by rw [hrd, show 1 + 2 * c.C.len = 2 * c.C.len + 1 by omega_using []]; simp,
      by rw [hwr]; simp, by simpa only [Nat.add_comm] using hpw, hwfit⟩
  obtain hrun : WP isa (Impl.EcKey.Compressed.X86_64.compress c).inline s fun s' =>
      (compressContract c.C).post s s' ∧ ∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s.gpr r := by
    apply front_ok hc hp
    intro g t F
    refine WP.mono (finish_ok hc F.scr F.out (by rw [F.wr, hwr]; simp) how hfit F.saved
      (decide (KeyOk c s)) (by simp only [F.flag, mask, decide_eq_true_eq])) fun s' ⟨hout, hret, hsave⟩ => ?_
    refine ⟨?_, fun r hr => (hsave r hr).trans (F.original r hr)⟩
    change (match Spec.EcKey.compressPublicKey c.C
      (Spec.EcKey.bytesAt s.mem (s.gpr .rsi) (2 * c.C.len + 1)) with
      | some bs => _
      | none => _)
    rw [compress_key]
    rw [F.x, F.y] at hout
    change Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) (c.C.len + 1) = _ at hout
    simp only [decide_eq_true_eq] at hret hout
    by_cases hk : KeyOk c s
    · rw [ite_eq_left hk] at hret hout ⊢
      exact ⟨hret, hout⟩
    · rw [ite_eq_right hk] at hret hout ⊢
      exact ⟨hret, hout⟩
  obtain ⟨t, s', he, hpost, hsave⟩ := hrun
  obtain F := (Exec.regions he (Code.noCalls_inline hi)).2.2
  refine ⟨t, s', he, abiPreserved_of_exec (by rw [Code.allInstrs_inline]; exact hmx) he
    ⟨fun r hr => ?_, ?_⟩, hpost⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsave _ (by decide)
    · exact hsave _ (by decide)
    · exact Exec.gpr (Code.clobbers_rsp_of_inlineOk hi) he
    · exact hsave _ (by decide)
    · exact hsave _ (by decide)
    · exact hsave _ (by decide)
    · exact hsave _ (by decide)
  · rw [hwr] at F
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hro
      · exact hrw) (by decide)

theorem compress_post_patch (C : Curve) (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (compressContract C).pre s) (hc : Clear (hole (s.gpr .rsp)) s)
    (hp : (compressContract C).post s b) :
    (compressContract C).post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain hn : C.len + 1 ≤ 2 ^ 64 := by
    obtain ⟨_, _, _, _, _, _, _, hf, _⟩ := hs
    omega_using [hf]
  obtain hb := Clear.wr_bytes hc (p := s.gpr .rdi) (n := C.len + 1)
    (by rw [hs.2.1]; simp) hn
  simpa only [compressContract, State.patch_gpr, VG.X86_64.EcKey.bytesAt_patch hb] using hp

end VG.Proof.EcKey.Compressed.X86_64
