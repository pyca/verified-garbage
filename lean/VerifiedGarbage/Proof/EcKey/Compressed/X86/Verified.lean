module

public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Impl.EcKey.Compressed.X86
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Pre
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Front
import VerifiedGarbage.Proof.EcKey.X86.Finish
import VerifiedGarbage.Proof.Ecdsa.X86.Finish
import VerifiedGarbage.Proof.Ecdsa.X86.Fixed
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.EcKey.Compressed.Parity
import VerifiedGarbage.Proof.EcKey.Compressed.Encode
import VerifiedGarbage.Proof.Ecdh.X86.Main
import VerifiedGarbage.Proof.Ecdsa.X86.Setup

/-! ### `EcKey.Compressed.X86.Finish`, which only this module used -/

section

/-! # Write a compressed point, clear failures, and restore x86 registers -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86/Tag.lean`, which only this module imported.
section

/-! # Encode the SEC 1 parity tag on 32-bit x86 -/

section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 VG.Proof.Ecdsa.X86 VG.Impl.Ecdsa.X86
open VG.Proof.EcKey.X86 (wp_store8S)

theorem tag32_byte (m : Mem) (base : Addr) (a n : Nat) (hn : 0 < n) (b : Bool) :
    ((((m.readW (off base a) 32 &&& 1) ||| 2) &&& mask32 (b = true)).setWidth 8) =
      if b then BitVec.ofNat 8 (2 + wordsVal m base a n % 2) else 0 := by
  rw [word32_parity m base a n hn]
  rcases Nat.mod_two_eq_zero_or_one (wordsVal m base a n) with h | h <;>
    cases b <;> simp [h, mask32] <;> decide

theorem tag_ok {c : Cfg} {s : State} {base : Addr} (hs : Scr s base size)
    (hy : c.sl Impl.Ecdh.X86.QY + 4 ≤ size) {o : BitVec 32}
    (hout : s.gpr .ebx = o) (hw : InRegions s.wr (o.setWidth 64) 1) (b : Bool)
    (hf : s.gpr .ecx = mask32 (b = true)) (hn : 0 < c.n) :
    WP isa (.block (Impl.EcKey.Compressed.X86.compressTag c)) s fun t =>
      t.mem (o.setWidth 64) =
        (if b then BitVec.ofNat 8 (2 + sv c base s Impl.Ecdh.X86.QY % 2) else 0) ∧
      Outside (o.setWidth 64) 0 1 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold Impl.EcKey.Compressed.X86.compressTag
  refine wp_movS (readSrc_sc hs hy) fun s₁ u₁ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₂ u₂ => ?_
  refine wp_orS rfl fun s₃ u₃ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₄ u₄ => ?_
  have K : Keeps [.eax] s s₄ := u₁.keeps.trans (u₂.keeps.trans (u₃.keeps.trans u₄.keeps))
  have hm : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have ho : s₄.gpr .ebx = o := (K.1 _ (by decide)).trans hout
  have ht : (s₄.gpr .eax).setWidth 8 =
      if b then BitVec.ofNat 8 (2 + sv c base s Impl.Ecdh.X86.QY % 2) else 0 := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr,
      u₃.other .ecx (by decide), u₂.other .ecx (by decide), u₁.other .ecx (by decide), hf]
    exact tag32_byte _ _ _ _ hn b
  refine wp_store8S (a := o.setWidth 64) (by change addr (s₄.gpr .ebx) 0 = _; rw [ho]; simp [addr])
    (by rw [K.2.2]; exact hw) fun t mt => WP.block_nil ?_
  refine ⟨?_, ?_, K.trans (mt.keeps _)⟩
  · rw [mt.mem, writeW8_self]
    simpa only [Reg8.reg] using ht
  · rw [mt.mem, ← hm]
    simpa [off, Reg8.reg] using (writeW8_outside s₄.mem (o.setWidth 64) (d := 0) ((s₄.gpr .eax).setWidth 8) (by decide))

end VG.Proof.EcKey.Compressed.X86
end

end

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.X86 VG.Impl.Weierstrass.X86 VG.Impl.Mont.X86
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 Spec.Weierstrass

theorem finish_eq (c : Cfg) : Impl.EcKey.Compressed.X86.compressFinish c =
    .mov .ecx (.mem (sc (c.sl FLAG))) :: .mov .ebx (.mem (Cfg.argOp 0)) ::
    (Impl.EcKey.Compressed.X86.compressTag c ++
    (storeBytes c.C.len c.n .ebx 1 (c.sl E) ++
    (([.mov .eax (.reg .ecx), .alu .and .eax (.imm 1)] : List Instr) ++ Cfg.restore))) := by
  simp only [Impl.EcKey.Compressed.X86.compressFinish, List.append_assoc, List.cons_append, List.nil_append]

theorem finish_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    {o : BitVec 32} (hout : readSrc s (.mem (Cfg.argOp 0)) = some o)
    (hofit : o.toNat + (1 + c.C.len) ≤ 2 ^ 32)
    (hw : (⟨o.setWidth 64, 1 + c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨o.setWidth 64, 1 + c.C.len⟩ ⟨base, size⟩)
    {g : Reg → BitVec 32} (hsv : ∀ rd ∈ Cfg.saved, s.mem.readW (off base rd.2) 32 = g rd.1) (b : Bool)
    (hf : flagW c base s = mask32 (b = true)) :
    WP isa (.block (Impl.EcKey.Compressed.X86.compressFinish c)) s fun t =>
      Spec.Ecdsa.bytesAt t.mem (o.setWidth 64) (1 + c.C.len) =
        (if b then BitVec.ofNat 8 (2 + sv c base s Impl.Ecdh.X86.QY % 2) ::
          toBytes c.C.len (sv c base s E) else List.replicate (1 + c.C.len) 0) ∧
      t.gpr .eax = (if b then 1 else 0) ∧
      (∀ rd ∈ Cfg.saved, t.gpr rd.1 = g rd.1) ∧
      t.gpr .esp = s.gpr .esp ∧ Outside (o.setWidth 64) 0 (1 + c.C.len) s.mem t.mem := by
  have hsz : size = 8192 := rfl
  have h7 := hc.n10
  have h0 := hc.n0
  have hE := sl_le c h7 (i := E) (by decide)
  have hY := sl_le c h7 (i := Impl.Ecdh.X86.QY) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have hn := hs.nowrap
  have hlhi := hc.len_hi
  have hl8 := hc.len8
  rw [finish_eq]
  refine wp_movS (readSrc_sc hs (d := c.sl FLAG) (by omega_using [h0, hF])) fun s₁ u₁ _ => ?_
  refine wp_movS (show readSrc s₁ (.mem (Cfg.argOp 0)) = some o by
    have hea : s₁.ea (Cfg.argOp 0) = s.ea (Cfg.argOp 0) := by
      show addr (s₁.gpr .esp) _ = addr (s.gpr .esp) _
      rw [u₁.other _ (by decide)]
    rw [← hout]; show s₁.load32 _ = s.load32 _
    rw [State.load32, State.load32, hea, u₁.rd, u₁.wr, u₁.mem]) fun s₂ u₂ _ => ?_
  have K₂ : Keeps [.ebx, .ecx] s s₂ := (u₁.keeps.mono (by simp)).trans (u₂.keeps.mono (by simp))
  have hs₂ := hs.of_keeps K₂ (by decide)
  have hb₂ : s₂.gpr .ebx = o := u₂.gpr
  have hc₂ : s₂.gpr .ecx = mask32 (b = true) := by rw [u₂.other _ (by decide), u₁.gpr, ← flagW, hf]
  have m₂ : s₂.mem = s.mem := u₂.mem.trans u₁.mem
  refine WP.block_append (WP.mono (tag_ok hs₂ (by omega_using [h0, hY]) hb₂
    (by rw [K₂.2.2]; exact ⟨_, hw, by simpa using Offset.contains_base (o.setWidth 64) (d := 0) (n := 1) (by omega_using []) (by decide)⟩)
    b hc₂ h0) fun s₃ ⟨L₃, O₃, K₃⟩ => ?_)
  simp only [sv, m₂] at L₃
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  have hb₃ : s₃.gpr .ebx = o := (K₃.1 _ (by decide)).trans hb₂
  have hc₃ : s₃.gpr .ecx = mask32 (b = true) := (K₃.1 _ (by decide)).trans hc₂
  have U₃ := O₃.unch_far (hd.symm.sub_right (Region.sub_prefix (by omega_using [])))
  have x₃ : wordsVal s₃.mem base (c.sl E) c.n = sv c base s E := by
    rw [U₃.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega_using [hE]) (by omega_using [hsz, hE]), m₂]
  refine WP.block_append (WP.mono (storeBytes_ok hs₃ (dst := .ebx) (d := 1) (a := c.sl E)
    (by decide) (by decide) b hc₃ hE (by omega_using [hl8]) hlhi (by rw [hb₃]; omega_using [hofit])
    (fun e m he => ⟨_, by rw [K₃.2.2, K₂.2.2]; exact hw, by
      rw [hb₃, Offset.add_add]; exact Offset.contains_base (o.setWidth 64) (by omega_using [he]) (by omega_using [hofit, he])⟩)
    (by rw [hb₃]; exact (hd.symm.sub_left (Offset.sub_base base hE)).sub_right (Offset.sub_base (o.setWidth 64) (d := 1) (by omega_using [])))) fun s₄ ⟨e₄, K₄, O₄⟩ => ?_)
  rw [hb₃, x₃] at e₄
  rw [hb₃] at O₄
  have hs₄ := hs₃.of_keeps K₄ (by decide)
  have U₄ := O₄.unch_far (hd.symm.sub_right (Offset.sub_base (o.setWidth 64) (d := 1) (by omega_using [])))
  have hsv₄ : ∀ rd ∈ Cfg.saved, s₄.mem.readW (off base rd.2) 32 = g rd.1 := by
    intro rd hrd
    have := saved_lt rd hrd
    have ap : ∀ w ∈ [(size, 2 ^ 64)], rd.2 + 4 ≤ w.1 ∨ w.1 + w.2 ≤ rd.2 := by
      intro w hw; obtain rfl := List.mem_singleton.mp hw; exact .inl (by omega)
    rw [Unch.readW32 U₄ ap (by omega_using [this]), Unch.readW32 U₃ ap (by omega_using [this]), m₂, hsv rd hrd]
  refine WP.mono (tail_ok hs₄ hsv₄ b (by rw [K₄.1 _ (by decide), hc₃]))
    fun t ⟨mt, ret, saved, others⟩ => ⟨?_, ret, saved, ?_, ?_⟩
  · have lead : Spec.Ecdsa.bytesAt s₄.mem (o.setWidth 64) 1 =
        [if b then BitVec.ofNat 8 (2 + sv c base s Impl.Ecdh.X86.QY % 2) else 0] := by
      rw [bytesAt_keep O₄ (Offset.base_disjoint (o.setWidth 64) (by omega_using []) (by omega_using [hofit])) (by omega_using [hofit]) (by omega_using [])]
      simpa [Spec.Ecdsa.bytesAt, sv] using congrArg (· :: []) L₃
    rw [mt, bytesAt_add, lead, e₄]
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      rw [Nat.add_comm 1, List.replicate_succ]; rfl
    · rfl
  · rw [others _ (by decide), K₄.1 _ (by decide), K₃.1 _ (by decide), K₂.1 _ (by decide)]
  · rw [mt, ← m₂]
    exact (O₃.mono (Nat.zero_le _) (by omega_using [])).trans ((O₄.shift (by omega_using [hofit])).mono (Nat.zero_le _) (by omega_using []))

end VG.Proof.EcKey.Compressed.X86

end

end


-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86/Main.lean`, which only this module imported.
section

section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86
open VG.Proof.Ecdh.X86 Spec.Weierstrass

theorem compress_key (c : Cfg) (s : State) :
    Spec.EcKey.compressPublicKey c.C
      (Spec.EcKey.bytesAt s.mem (ptr s 1) (2 * c.C.len + 1)) =
    if KeyOk c s then some (BitVec.ofNat 8 (2 + keyY c s % 2) :: toBytes c.C.len (keyX c s)) else none := by
  have hlen : (Spec.Ecdsa.bytesAt s.mem (ptr s 1) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]
    omega
  have hhead : (Spec.Ecdsa.bytesAt s.mem (ptr s 1) (1 + 2 * c.C.len)).head? =
      some (s.mem (ptr s 1)) := by rw [peer_bytes]; rfl
  have hx : ofBytes (((Spec.Ecdsa.bytesAt s.mem (ptr s 1) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      keyX c s := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
    rfl
  have hy : ofBytes ((Spec.Ecdsa.bytesAt s.mem (ptr s 1) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      keyY c s := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  have hv : Proof.Ecdh.Valid c.C (s.mem (ptr s 1)) (keyX c s) (keyY c s) ↔ KeyOk c s := by
    constructor
    · rintro ⟨h4, hx, hy, he⟩
      exact ⟨⟨⟨h4, hx⟩, hy⟩, he⟩
    · rintro ⟨⟨⟨h4, hx⟩, hy⟩, he⟩
      exact ⟨h4, hx, hy, he⟩
  change Spec.EcKey.compressPublicKey c.C
    (Spec.Ecdsa.bytesAt s.mem (ptr s 1) (2 * c.C.len + 1)) = _
  rw [show 2 * c.C.len + 1 = 1 + 2 * c.C.len by omega, compress_eq hlen hhead hx hy]
  simp only [hv]


def compressFront (c : Cfg) : Prog isa :=
  .seq (.block (c.setupWith Impl.EcKey.Compressed.X86.args))
    (.seq (.block (Impl.Ecdh.X86.Cfg.peerAt c 1)) (Impl.Ecdh.X86.Cfg.validate c))

theorem compressFront_ok {c : Cfg} (hc : CfgOk c) {s : State}
    (hp : InputPre c (1 + 2 * c.C.len) s) : WP isa (compressFront c) s (Front c s) := by
  have h := front_ok hc hp (rest := .block []) (fun _ F => WP.block_nil F)
  simpa only [compressFront, WP.seq_iff (M := isa), WP.block_nil_iff (M := isa)] using h

theorem compress_correct (c : Cfg) (hc : CfgOk c)
    (hsp : SpOk (Impl.EcKey.Compressed.X86.compress c) 28)
    (s : State) (hs : (compressContract c.C).pre s) :
    ∃ t s', Exec isa (Impl.EcKey.Compressed.X86.compress c) s t s' ∧
      abiPreserved s s' ∧ (compressContract c.C).post s s' := by
  have hp := codec_input (c := c) hs
  obtain ⟨hrd, hwr, how, hpo, hpw, hao, haw, hro, hrw, hfit, hpk, hws, hsf, hlo, hso, hsw⟩ := hs
  simp only [Bool.false_eq_true, ite_false] at hrd hwr
  have hfront : SpOk (compressFront c) 28 := hsp.left.seq (hsp.right.left.seq hsp.right.right.left)
  have hrun : WP isa (Impl.EcKey.Compressed.X86.compress c) s fun u =>
      (compressContract c.C).post s u ∧
      (∀ rd ∈ Cfg.saved, u.gpr rd.1 = s.gpr rd.1) ∧ u.gpr .esp = s.gpr .esp := by
    change WP isa ([.block (c.setupWith Impl.EcKey.Compressed.X86.args),
      .block (Impl.Ecdh.X86.Cfg.peerAt c 1)].foldr .seq
      (.seq (Impl.Ecdh.X86.Cfg.validate c) (.block (Impl.EcKey.Compressed.X86.compressFinish c)))) s _
    rw [WP.split]
    refine WP.seq (WP.mono (WP.spFrame hfront hlo (compressFront_ok hc
      (by simpa only [Nat.add_comm] using hp))) fun t ⟨F, W⟩ => ?_)
    have hin : InRegions (s.rd ++ s.wr) (argAddr s 0) 4 :=
      ⟨_, by rw [hrd, hwr]; simp, arg_containsN (k := 3) (by omega) (by decide)⟩
    have hdarg : ∀ r ∈ s.wr ++ [below (s.gpr .esp) 28], Region.Disjoint ⟨argAddr s 0, 4⟩ r := by
      intro r hr
      rw [hwr] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hao.sub_left (arg_subN (k := 3) (by omega) (by decide))
      · exact haw.sub_left (arg_subN (k := 3) (by omega) (by decide))
      · exact (below_disjoint_args hlo (by omega) (by decide)).symm
    have hout := argLoad_frame hin hdarg F.esp (by rw [F.rd, F.wr]) W
    refine WP.mono (finish_ok hc F.scr hout (by omega)
      (by rw [F.wr, hwr]; simp [Nat.add_comm]) (by simpa only [Nat.add_comm] using how)
      F.saved (decide (KeyOk c s)) (by simp only [F.flag, decide_eq_true_eq]))
      fun u ⟨bytes, ret, saved, esp, _⟩ => ?_
    refine ⟨?_, saved, esp.trans F.esp⟩
    dsimp only [compressContract]
    rw [compress_key, BitVec.setWidth_append_eq_right]
    rw [F.x, F.y] at bytes
    change Spec.EcKey.bytesAt u.mem ((arg s 0).setWidth 64) (1 + c.C.len) = _ at bytes
    simp only [decide_eq_true_eq] at ret bytes
    by_cases hk : KeyOk c s
    · rw [ite_eq_left hk] at ret bytes ⊢
      exact ⟨ret, by simpa only [Nat.add_comm] using bytes⟩
    · rw [ite_eq_right hk] at ret bytes ⊢
      exact ⟨ret, by simpa only [Nat.add_comm] using bytes⟩
  obtain ⟨t, u, he, ⟨hpost, saved, esp⟩, W⟩ := WP.spFrame hsp hlo hrun
  refine ⟨t, u, he, ⟨?_, ?_⟩, hpost⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact saved (.ebx, 0) (by decide)
    · exact saved (.esi, 4) (by decide)
    · exact saved (.edi, 8) (by decide)
    · exact saved (.ebp, 12) (by decide)
    · exact esp
  · refine W.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rw [hwr] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hro
    · exact hrw
    · exact (below_disjoint_ret hlo).symm

end VG.Proof.EcKey.Compressed.X86
end

end

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Weierstrass.X86

theorem compress_verified {c : Cfg} (hc : CfgOk c) (I : Spec.EcKey.Instance) (hC : c.C = I.curve)
    (hsp : SpOk (Impl.EcKey.Compressed.X86.compress c) 28)
    (hct : ConstantTime isa (compressContract c.C).pre (compressContract c.C).pub
      (Impl.EcKey.Compressed.X86.compress c))
    (hsig : ∃ s, (I.compressPublicKeyContract abi 28).pre s) :
    Verified target (Impl.EcKey.Compressed.X86.compress c) (I.compressPublicKeyContract abi 28) := by
  have himp := compress_implies I hsig
  have hsat := himp.sat_left
  have localSat : ∃ s, (compressContract c.C).pre s := by
    obtain ⟨s, hs⟩ := hsat
    refine ⟨s.withRegions (codecRd (2 * I.curve.len + 1) s) (codecWr (I.curve.len + 1) s), ?_⟩
    rw [hC]
    exact codecWide_pre hs
  have localVerified : Verified target (Impl.EcKey.Compressed.X86.compress c) (compressContract I.curve) := by
    rw [← hC]
    exact Verified.of_correct (compress_correct c hc hsp) hct (.refl localSat)
  apply Verified.of_implies (Verified.narrowTo localVerified
    (codecRd (2 * I.curve.len + 1)) (codecWr (I.curve.len + 1))
    (fun _ h => codecWide_pre h) ?_ ?_ ?_ ?_ hsat) himp
  · intro s h a n ⟨r, hr, hcontains⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hcontains⟩
    simp only [codecRd, codecWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp
  · intro s h a n ⟨r, hr, hcontains⟩
    rw [h.2.1]
    refine ⟨r, ?_, hcontains⟩
    simp only [codecWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [compressContract, arg_withRegions, State.withRegions_mem, State.withRegions_gpr] using h
  · intro s t _ _ h
    simpa only [compressContract, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.EcKey.Compressed.X86
