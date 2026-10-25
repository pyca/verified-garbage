module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE.Decompress
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontCall
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Peer
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Flags
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Bits
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.BytesLen
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# SEC 1 point decompression on PPC64LE: reading the compressed key

`decompressTag_ok`: the tag (the byte `r12` points to) to `D`'s first word,
and the mask of it being `02` or `03`; `decompressPeer_ok`: `decompressPeer`
stores `R² mod p` and `b R mod p`, reads `x` into the hash's slot, the tag
into `D`, and ands into the flag the masks of the tag and of `x < p`, as
ECDH's `peer_ok` (`Proof/Ecdh/PPC64LE/Peer.lean`).
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Proof.Ecdh.PPC64LE VG.Spec.Weierstrass
open VG.Impl.Ecdh.PPC64LE (R2P BP)

/-- `-((((b | 1) ^ 3) - 1) >>> 63)` is the mask of `b ∈ {2, 3}`, for a byte
`b`. -/
theorem tag_mask (b : BitVec 8) :
    BitVec.ofNat 64 0 - (((b.setWidth 64 ||| BitVec.ofNat 64 1) ^^^ BitVec.ofNat 64 3) - BitVec.ofNat 64 1) >>> 63 =
      mask64 (b = 2 ∨ b = 3) := by
  revert b; decide +kernel

/-- The tag to `D`'s first word, and the mask `r5` of it being `02` or `03`. -/
theorem decompressTag_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Ws s base size)
    (h3 : At s base .r3 0) (hin : InRegions (s.rd ++ s.wr) (s.gpr .r12) 1) (hD : c.sl D + 8 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.PPC64LE.decompressTag c)) s fun s' =>
      s'.gpr .r5 = mask64 (s.mem (s.gpr .r12) = 2 ∨ s.mem (s.gpr .r12) = 3) ∧ Kp [.r4, .r5] s s' ∧
      s'.mem = s.mem.writeW (off base (c.sl D)) ((s.mem (s.gpr .r12)).setWidth 64) := by
  simp only [Impl.EcKey.Compressed.PPC64LE.decompressTag]
  refine wp_step (exec_lbz (by decide) (by decide) (by rw [BitVec.add_zero]; exact hin)) ?_
  refine wp_step (std0_ok (hs.write _ _) (h3.write _) (by decide) (sl_al c D) hD) ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_logic ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_logic ?_
  refine wp_step (exec_subi (by decide) (by decide)) ?_
  refine wp_step (exec_lsr_d (by decide)) ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_sub (WP.block_nil ⟨?_, ?_, ?_⟩)
  · simp only [write_gpr, ite_true, reduceCtorEq, ite_false, BitVec.add_zero, read_one]
    exact tag_mask _
  · exact ((((((((((Kp.write _ _ (by decide)).trans (Kp.store _ _ _)).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide)))
  · simp only [write_mem, write_gpr, ite_true, BitVec.add_zero, read_one]

theorem decompressPeer_eq (c : Cfg) : Impl.EcKey.Compressed.PPC64LE.decompressPeer c =
    (Impl.Ecdh.PPC64LE.Cfg.consts c).flatMap (fun (i, x) => VG.Impl.Mont.PPC64LE.setConst c.n (c.sl i) x) ++
    (.addi .r6 .r12 1 :: (loadBytes c.C.len c.n (c.sl E) .r6 ++
    (Impl.EcKey.Compressed.PPC64LE.decompressTag c ++ (c.andFlag ++
    Impl.Ecdh.PPC64LE.Cfg.checkLtP c (c.sl E))))) := by
  simp only [Impl.EcKey.Compressed.PPC64LE.decompressPeer, List.append_assoc, List.cons_append,
    List.nil_append]

variable {c : Cfg}

/-- The constants, the key's `x` and tag, and the checks of the tag and `x`,
for a key that `r12` points to. -/
theorem decompressPeer_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base)
    (hqfit : (s.gpr .r12).toNat + (1 + c.C.len) ≤ 2 ^ 64)
    (hin : (⟨s.gpr .r12, 1 + c.C.len⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨s.gpr .r12, 1 + c.C.len⟩ ⟨base, size⟩) (hmp : sv c base s MP = c.C.p) :
    WP isa (.block (Impl.EcKey.Compressed.PPC64LE.decompressPeer c)) s fun s' =>
      WsReg s' base ∧ Kp peerClob s s' ∧
      Unch base (slW c [R2P, BP, E, D] ++ [(c.sl FLAG, 8)]) s.mem s'.mem ∧
      sv c base s' R2P = c.R * c.R % c.C.p ∧ sv c base s' BP = c.mont c.C.b ∧
      sv c base s' E = ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .r12 + BitVec.ofNat 64 1) c.C.len) ∧
      word s'.mem base (c.sl D) = (s.mem (s.gpr .r12)).setWidth 64 ∧
      flagW c base s' = flagW c base s &&& mask64 (s.mem (s.gpr .r12) = 2 ∨ s.mem (s.gpr .r12) = 3) &&&
        mask64 (sv c base s' E < c.C.p) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hw.nowrap
  have hsz : size = 8192 := rfl
  have hpl := hc.p_lt
  have hp3 := hc.p_ge
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  have hF : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  have hR2 := sl_le c h7 (i := R2P) (by decide)
  have hB := sl_le c h7 (i := BP) (by decide)
  have hD := sl_le c h7 (i := D) (by decide)
  have hE := sl_le c h7 (i := E) (by decide)
  have hM := sl_le c h7 (i := MP) (by decide)
  generalize hqa : s.gpr .r12 = qa at hqfit hin hd ⊢
  rw [decompressPeer_eq]
  -- The constants.
  refine wp_append (WP.mono (setupConsts_ok hc (Impl.Ecdh.PPC64LE.Cfg.consts c) hw (fun ix hix => by
      simp only [Impl.Ecdh.PPC64LE.Cfg.consts, List.mem_cons, List.not_mem_nil, or_false] at hix
      rcases hix with rfl | rfl
      · exact ⟨show R2P < 45 by decide, Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hpl⟩
      · exact ⟨show BP < 45 by decide, Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hpl⟩)
      (show [R2P, BP].Nodup by decide))
    fun s₁ ⟨e₁, k₁, U₁⟩ => ?_)
  have hw₁ := hw.of_kp k₁
  have U₁' : Unch base (slW c [R2P, BP]) s.mem s₁.mem := U₁
  -- `public + 1`
  refine wp_step (exec_addi (by decide) (by decide)) ?_
  have k₂ : Kp [.r6, .r11] s (s₁.write .r6 (s₁.gpr .r12 + BitVec.ofNat 64 1)) :=
    (k₁.mono (by decide)).trans (Kp.write _ _ (by decide))
  have hq₁ : s₁.gpr .r12 = qa := by rw [k₁.gpr _ (by decide), hqa]
  have hrw : ∀ {t : State} {rs : List Reg}, Kp rs s t → t.rd ++ t.wr = s.rd ++ s.wr := fun K => by
    rw [K.rd, K.wr]
  have O₁ : Outside base 0 4096 s.mem s₁.mem := U₁'.outside fun w hw => by
    simp only [slW, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> exact ⟨Nat.zero_le _, by dsimp only; omega_arith⟩
  have hfit₁ : (qa + BitVec.ofNat 64 1).toNat + c.C.len ≤ 2 ^ 64 := by
    rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  -- `x`
  refine wp_append (WP.mono (setupLoad_ok hc (s := s) (i := E) (src := .r6) (p := qa + BitVec.ofNat 64 1)
    (hw₁.of_kp (Kp.write _ (d := .r6) (rs := [.r6]) _ (by decide))) (by decide) (by decide)
    (by simp only [write_gpr, ite_true, hq₁]) hfit₁
    (fun e he => ⟨_, by rw [hrw k₂]; exact hin, by
      rw [Offset.add_add]; exact Offset.contains_base qa (by omega_arith) (by omega_arith)⟩)
    (hd.sub_left (Offset.sub_base qa (by omega_arith))) (by simp only [write_mem]; exact O₁))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_)
  have K₃ : Kp [.r6, .r8, .r9, .r11] s s₃ :=
    (k₂.mono (by decide)).trans (k₃.mono (by decide))
  have hw₃ := hw.of_kp K₃
  have hq₃ : s₃.gpr .r12 = qa := by rw [K₃.gpr _ (by decide), hqa]
  have O₃' : Outside base 0 size s.mem s₃.mem :=
    (O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₃.mono (Nat.zero_le _) (by omega_arith))
  -- the tag
  refine wp_append (WP.mono (decompressTag_ok c hw₃.ws hw₃.at3
    ⟨_, by rw [hrw K₃]; exact hin, by
      have := Offset.contains_base qa (d := 0) (n := 1) (k := 1 + c.C.len) (by omega_arith) (by omega_arith)
      rw [BitVec.add_zero] at this; rw [hq₃]; exact this⟩ (by omega_arith)) fun s₄ ⟨m₄, k₄, h₄⟩ => ?_)
  rw [hq₃] at m₄ h₄
  have hw₄ := hw₃.of_kp k₄
  have lead₃ : s₃.mem qa = s.mem qa := by
    have := keep_of_disjoint' O₃' hd (by omega_arith) (i := 0) (by omega_arith) (by omega_arith)
    rwa [BitVec.add_zero] at this
  rw [lead₃] at m₄ h₄
  have O₄ : Outside base (c.sl D) 8 s₃.mem s₄.mem := by rw [h₄]; exact writeW_outside _ _ _ (by omega_arith)
  -- the flag `&=` the tag's mask
  refine wp_append (WP.mono (andFlag_ok c hw₄.ws hw₄.at3 hF) fun s₅ ⟨f₅, k₅, m₅⟩ => ?_)
  rw [m₄] at f₅
  have hw₅ := hw₄.of_kp k₅
  have O₅ : Outside base (c.sl FLAG) 8 s₄.mem s₅.mem := by rw [m₅]; exact writeW_outside _ _ _ (by omega_arith)
  -- `x < p`
  refine WP.mono (checkLtP_ok c hw₅.ws hw₅.at3 (by omega_arith) (by omega_arith) hF) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_
  -- The slots.
  have U₃₆ : Unch base ([(c.sl D, 8)] ++ [(c.sl FLAG, 8)] ++ [(c.sl FLAG, 8)]) s₃.mem s₆.mem :=
    (O₄.unch.trans O₅.unch).trans O₆.unch
  have apDF : ∀ {i}, i < 45 → i ≠ FLAG → i ≠ D →
      ∀ w ∈ [(c.sl D, 8)] ++ [(c.sl FLAG, 8)] ++ [(c.sl FLAG, 8)],
        c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := fun hi hf hD' =>
    apart_append (apart_append (fun w hw => by
      rw [List.mem_singleton.mp hw]; have := sl_apart c hD'; dsimp only; omega_arith) (apart_flag h0 hf))
      (apart_flag h0 hf)
  have v₆ : ∀ {i}, i < 45 → i ≠ FLAG → i ≠ D → sv c base s₆ i = sv c base s₃ i := fun hi hf hD' =>
    sv_unch U₃₆ h7 hn hi (apDF hi hf hD')
  have v₃ : ∀ {i}, i < 45 → i ≠ E → sv c base s₃ i = sv c base s₁ i := fun hi hl =>
    sv_unch O₃.unch h7 hn hi (apart_slW (c := c) (l := [E]) (by simpa using hl))
  have v₁ : ∀ {i}, i < 45 → i ∉ [R2P, BP] → sv c base s₁ i = sv c base s i := fun hi hl =>
    sv_unch U₁' h7 hn hi (apart_slW (c := c) (l := [R2P, BP]) hl)
  have xE : sv c base s₆ E = ofBytes (Spec.Ecdsa.bytesAt s.mem (qa + BitVec.ofNat 64 1) c.C.len) := by
    rw [v₆ (by decide) (by decide) (by decide)]; exact e₃
  have hsD := sl_apart c (i := D) (j := FLAG) (by decide)
  refine ⟨hw₅.of_kp k₆, ?_, ?_, ?_, ?_, xE, ?_, ?_⟩
  · exact (((K₃.mono (by decide)).trans (k₄.mono (by decide))).trans (k₅.mono (by decide))).trans
      (k₆.mono (by decide))
  · refine ((U₁'.trans O₃.unch).trans U₃₆).cover fun w hw => ?_
    simp only [slW, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      or_assoc] at hw
    have h8 : 8 ≤ 8 * c.n := by omega_arith
    rcases hw with h | h | h | h | h | h <;> subst h
    · exact ⟨_, by simp [slW], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [slW], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [slW], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(c.sl D, 8 * c.n), by simp [slW], Nat.le_refl _, by dsimp only; omega_arith⟩
    · exact ⟨_, by simp [slW], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [slW], Nat.le_refl _, Nat.le_refl _⟩
  · rw [v₆ (by decide) (by decide) (by decide), v₃ (by decide) (by decide)]
    exact e₁ (R2P, c.R * c.R % c.C.p) List.mem_cons_self
  · rw [v₆ (by decide) (by decide) (by decide), v₃ (by decide) (by decide)]
    exact e₁ (BP, c.mont c.C.b) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  · have U₄₆ : Unch base ([(c.sl FLAG, 8)] ++ [(c.sl FLAG, 8)]) s₄.mem s₆.mem := O₅.unch.trans O₆.unch
    rw [U₄₆.word (fun w hw => by
      simp only [List.mem_append, List.mem_singleton, or_self] at hw; subst hw; dsimp only; omega_arith) (by omega_arith),
      h₄, word_writeW_self]
  · have mp₅ : wordsVal s₅.mem base (c.sl MP) c.n = c.C.p := by
      rw [sv_unch O₅.unch h7 hn (i := MP) (by decide) (apart_flag h0 (by decide)),
        sv_unch O₄.unch h7 hn (i := MP) (by decide) (fun w hw => by
          rw [List.mem_singleton.mp hw]; have := sl_apart c (i := MP) (j := D) (by decide); dsimp only; omega_arith)]
      exact (v₃ (by decide) (by decide)).trans ((v₁ (by decide) (by decide)).trans hmp)
    have e₅ : wordsVal s₅.mem base (c.sl E) c.n = sv c base s₆ E :=
      (sv_unch O₆.unch h7 hn (i := E) (by decide) (apart_flag h0 (by decide))).symm
    have hFl := sl_le c h7 (i := FLAG) (by decide)
    have fl₄ : flagW c base s₄ = flagW c base s := by
      have ap : ∀ w ∈ slW c [R2P, BP] ++ [(c.sl E, 8 * c.n)] ++ [(c.sl D, 8)],
          c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := fun w hw => by
        simp only [slW, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false, or_assoc] at hw
        rcases hw with h | h | h | h <;> subst h <;> dsimp only
        · have := sl_lt c (i := R2P) (j := FLAG) (by decide); omega_arith
        · have := sl_lt c (i := BP) (j := FLAG) (by decide); omega_arith
        · have := sl_lt c (i := E) (j := FLAG) (by decide); omega_arith
        · have := sl_lt c (i := D) (j := FLAG) (by decide); omega_arith
      exact ((U₁'.trans O₃.unch).trans O₄.unch).word ap (by omega_arith)
    rw [f₆, f₅, fl₄, e₅, mp₅]

end VG.Proof.EcKey.Compressed.PPC64LE
