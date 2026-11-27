module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Tag
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTAbsorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTFin
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Flush
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamFinish
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Tag
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTAbsorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Flush
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamFinish
public import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Crypt
public import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Crypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
meta import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
public import VerifiedGarbage.Proof.Modes.PPC64LE.Seq
public import VerifiedGarbage.Proof.Sm4.SboxTable
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Init
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Init
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Sm4.CtrCipher
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Aes.SboxSpec
meta import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
meta import VerifiedGarbage.Proof.Framework.Inline
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Modes.PPC64LE.Seq
meta import VerifiedGarbage.Proof.Sm4.SboxTable
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.StreamCrypt
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamInit
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
public import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Tag
meta import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.StreamCrypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamInit
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
meta import VerifiedGarbage.Spec.Gcm
meta import VerifiedGarbage.Spec.Sm4.Gcm.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Gcm.Compose
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Tag

/-! ### `Sm4Gcm.PPC64LE.StreamFinish`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.PPC64LE.FinTag`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on PPC64LE: the tag after the last piece (`finTag o`)

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/FinTag.lean`), with SM4's tag: `finTag o` pads and absorbs the buffered
bytes (`flush`), of the text if there is any and else of the additional
data, then puts the tag into `W + o` (`tag`), for `aad_len` (`r22`) bytes
of additional data and `text_len` (`r23`) of text (`finTag_ok`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)
open VG.Proof.AesGcm.PPC64LE (Env Lay Keeps tFrame flush_ok j_tFrame eval_zero and15 blockAt_frame
  WP.with_rdwr)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput ghash ghashFrom blocks zeros padLen toBytes ofBytes)
open VG.Proof.Gcm (Absorbed lensBlock padded)

/-- `tFrame` is within `tagFrame`. -/
theorem tFrame_sub {st w x : Addr} {o : Nat} :
    ∀ r ∈ tFrame st w 16, ∃ r' ∈ tagFrame st w x o, Region.Sub r r' := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self .., by simpa using Offset.sub_base st (show 16 + 16 ≤ 32 by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

theorem t_tagFrame {st w x : Addr} {o : Nat} {m m' : Mem} (h : Frame (tFrame st w 16) m m') :
    Frame (tagFrame st w x o) m m' := h.sub tFrame_sub

/-- After `finTag o`, from `m₀`. -/
structure FinOut (V : Reg → BitVec 64) (sp : Addr) (o : Nat) (H : Block) (a ct : List Byte) (m₀ : Mem)
    (s : State) : Prop where
  env : Env V sp s
  out : Absorbed m₀ (V .r30 + BitVec.ofNat 64 16) (V .r30 + BitVec.ofNat 64 32) H (ghashInput a ct) →
    bytesAt s.mem (V .r31 + BitVec.ofNat 64 o) 16 =
      toBytes (ghashFrom H (ghash H (blocks (padded a ct))) [ofBytes (lensBlock (V .r22).toNat ct.length)]
        ^^^ ciphOf m₀ (V .r29) (blockAt m₀ (V .r30)))
  frame : Frame (tagFrame (V .r30) (V .r31) (V .r28) o) m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r30) (V .r31))
  (X : XOk (V .r29) (V .r30) (V .r31) (V .r28))
include L X

theorem finTag_ok [VG.Proof.Gcm.PPC64LE.GhashLaw] {o : Nat} (ho : o = 0 ∨ o = 112) {H : Block} {a ct : List Byte} {s : State}
    (he : Env V sp s) (hxw : Covers [xR (V .r28)] s.wr)
    (hH : blockAt s.mem (V .r29 + BitVec.ofNat 64 240) = H)
    (ha : a.length % 16 = (V .r22).toNat % 16) (hP : (V .r23).toNat = ct.length) :
    WP isa (finTag o) s (FinOut V sp o H a ct s.mem) := by
  have h22 := he.fr .r22 (by decide)
  have h23 := he.fr .r23 (by decide)
  -- `r26`: the length of the buffered bytes, modulo 16
  have mid : WP isa (.ite (.zero .d .r23) (.block [.li .r0 15, .logic .and .r26 .r22 .r0])
      (.block [.li .r0 15, .logic .and .r26 .r23 .r0])) s fun s₂ =>
      s₂.gpr .r26 = BitVec.ofNat 64 ((ghashInput a ct).length % 16) ∧
        (∀ r, r ≠ .r0 → r ≠ .r26 → s₂.gpr r = s.gpr r) ∧ Keeps s s₂ := by
    refine WP.ite _ (eval_zero (he.ofNat (r := .r23) (by decide)) (V .r23).isLt) (fun ht => ?_) (fun hf => ?_)
    · have hc : ct = [] := List.eq_nil_of_length_eq_zero (by rw [← hP]; simpa using ht)
      have e : (ghashInput a ct).length % 16 = (V .r22).toNat % 16 := by
        rw [hc, Proof.Gcm.ghashInput_nil, ha]
      have hand := and15 (V .r22)
      rw [e]
      crun [h22, hand]
      exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    · have hc : ct ≠ [] := fun e => by subst e; simp only [List.length_nil] at hP; simp [hP] at hf
      have e : (ghashInput a ct).length % 16 = (V .r23).toNat % 16 := by
        rw [Proof.Gcm.ghashInput_of_ne hc, List.length_append, List.length_append, Proof.Gcm.length_zeros, hP]
        have := Proof.Gcm.length_pad_mod a.length; omega_using [this]
      have hand := and15 (V .r23)
      rw [e]
      crun [h23, hand]
      exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono mid fun s₂ ⟨h26₂, hg₂, hk₂⟩ => ?_)
  have he₂ := he.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
  refine WP.seq (WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl) (x := ghashInput a ct) (H := H)
    ⟨he₂, by rw [hk₂.mem]; exact hH⟩ h26₂)) fun s₄ ⟨hfl, _, hwr₄, _⟩ => ?_)
  have hf₄ := hfl.frame
  rw [hk₂.mem] at hf₄
  -- the lengths
  have h₅ : WP isa (.block [mov .r24 .r22, mov .r26 .r23]) s₄ fun s₅ =>
      s₅.gpr .r24 = V .r22 ∧ s₅.gpr .r26 = V .r23 ∧ (∀ r, r ≠ .r24 → r ≠ .r26 → s₅.gpr r = s₄.gpr r) ∧
        Keeps s₄ s₅ := by
    have e22 := hfl.env.fr .r22 (by decide)
    have e23 := hfl.env.fr .r23 (by decide)
    crun [mov, BitVec.or_self, e22, e23]
    exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₅ fun s₅ ⟨h24₅, h26₅, hg₅, hk₅⟩ => ?_)
  have he₅ := hfl.env.keep (fun r hr => hg₅ r (by revert r; decide) (by revert r; decide)) hk₅.sp hk₅.rd hk₅.wr
  refine WP.mono (tag_ok L X ho he₅ (by rw [hk₅.wr, hwr₄, hk₂.wr]; exact hxw) (H := H)
    (by rw [hk₅.mem]; exact hfl.hH) rfl) fun s₆ tg => ?_
  rw [h24₅, h26₅, hP, hk₅.mem] at tg
  refine ⟨tg.env, fun hab => ?_, (t_tagFrame hf₄).trans tg.frame⟩
  rw [tg.out]
  have hw := (hfl.abs (by rw [hk₂.mem]; exact hab)).whole_eq (by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
  rw [show ghashInput a ct ++ zeros (padLen (ghashInput a ct).length) = padded a ct from rfl] at hw
  rw [hw, ciph_frame hf₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.cs.sub_right (Lay.stSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))),
    blockAt_frame hf₄ (j_tFrame L)]

end

end VG.Proof.Sm4Gcm.PPC64LE

end

end

/-!
# SM4-GCM on PPC64LE: `vg_sm4_gcm_stream_finish`

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/StreamFinish.lean`), with SM4's tag: the entry saves our caller's
registers and keeps the arguments in `r20`–`r30` (`fin1_wp`); `finTag 0`
puts the tag into `W` (`fin_tag`, `fin_out`), and `tagOut` copies it to
`tag` (`streamFinish_wp`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov tagOut)
open VG.Proof.AesGcm.PPC64LE (Env Lay Perm Entered SavedAt savedR save_ok restore_ok covers_mem
  covers_prefix covers_off bytesAt_frame blockAt_frame ctx_saved ctxH_keep saved_w toNat_mod16 WP.forall_det
  WP.with_rdwr Lay.saved_st tagOut_ok lensBlock_mod toNat_of_eq)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ghashInput fullTag)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed)

section
variable {s₀ : State} (h : finPre s₀)
include h

theorem finLay : Lay (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r8) := by
  obtain ⟨-, -, dcs, -, dcw, -, dsw, -, fc, fs, -, fw, -⟩ := h
  have fw' : (s₀.gpr .r8).toNat + 288 ≤ 2 ^ 64 := fw
  exact Lay.of fc fs (by omega_using [fw']) dcs (dcw.sub_right (Region.sub_prefix (by decide)))
    (dsw.sub_right (Region.sub_prefix (by decide)))

theorem finX : XOk (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r8) (s₀.gpr .r9) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, dcx, dsx, -, dwx, fx⟩ := h
  exact ⟨fx, dcx, dsx, dwx⟩

theorem fin_W' : Covers [⟨s₀.gpr .r8, scrBytes⟩] s₀.wr := by
  rw [h.2.1]; exact covers_mem (by simp)

theorem fin_W : Covers [⟨s₀.gpr .r8, 288⟩] s₀.wr := covers_prefix (fin_W' h) (by decide)

theorem fin_X : Covers [xR (s₀.gpr .r9)] s₀.wr := by
  rw [h.2.1]; exact covers_mem (by simp)

end

/-- After the entry of `finish`, from `s₀`. -/
structure SF1 (s₀ s₁ : State) : Prop where
  en : Entered s₀ (s₀.gpr .r8) s₁
  r31 : s₁.gpr .r31 = s₀.gpr .r8
  r30 : s₁.gpr .r30 = s₀.gpr .r4
  r29 : s₁.gpr .r29 = s₀.gpr .r3
  r22 : s₁.gpr .r22 = s₀.gpr .r5
  r23 : s₁.gpr .r23 = s₀.gpr .r6
  r20 : s₁.gpr .r20 = s₀.gpr .r7
  r28 : s₁.gpr .r28 = s₀.gpr .r9

theorem fin1_wp {s₀ : State} (hW : Covers [⟨s₀.gpr .r8, 288⟩] s₀.wr) :
    WP isa (.block finEntry) s₀ (SF1 s₀) := by
  refine WP.block_append (WP.mono (save_ok (b := .r8) (by decide) hW) fun s₁ ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  have e3 : s₁.gpr .r3 = s₀.gpr .r3 := hg _ (by decide) (by decide)
  have e4 : s₁.gpr .r4 = s₀.gpr .r4 := hg _ (by decide) (by decide)
  have e5 : s₁.gpr .r5 = s₀.gpr .r5 := hg _ (by decide) (by decide)
  have e6 : s₁.gpr .r6 = s₀.gpr .r6 := hg _ (by decide) (by decide)
  have e7 : s₁.gpr .r7 = s₀.gpr .r7 := hg _ (by decide) (by decide)
  have e9 : s₁.gpr .r9 = s₀.gpr .r9 := hg _ (by decide) (by decide)
  crun [mov, BitVec.or_self, e3, e4, e5, e6, e7, e9, h31]
  refine ⟨⟨fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [hg],
    ⟨hk.rd, hk.wr, hk.sp, hk.lr⟩, hsv, hf⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [h31]

/-- The environment after the entry. -/
theorem fin_env {s₀ s₁ : State} (h : finPre s₀) (h1 : SF1 s₀ s₁) : Env s₁.gpr s₀.sp s₁ := by
  obtain ⟨hrd, hwr, -⟩ := h
  have perm : Perm (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r8) s₁ :=
    (⟨covers_mem (by rw [hrd]; simp), covers_mem (by rw [hwr]; simp),
      covers_prefix (covers_mem (r := ⟨s₀.gpr .r8, scrBytes⟩) (by rw [hwr]; simp)) (by decide)⟩ :
      Perm (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r8) s₀).of_eq h1.en.keeps.rd h1.en.keeps.wr
  exact ⟨fun _ _ => rfl, h1.en.keeps.sp, by rw [h1.r29, h1.r30, h1.r31]; exact perm⟩

section
variable {c st w x : Addr} (L : Lay c st w) (X : XOk c st w x)
include L X

theorem saved_tagFrame {o : Nat} (ho : o = 0 ∨ o = 112) : ∀ r ∈ tagFrame st w x o, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using L.saved_st (d := 0) (k := 32) (by decide)
  · exact saved_w (by decide) (.inl (by decide))
  · exact saved_w (by omega_using [ho]) (.inl (by omega_using [ho]))
  · exact X.wx.sub_left (Lay.wSub (by decide))

end

/-- The tag, for a state that represents `a` and `ct`, from a memory `m₀`
that differs from the entry's only apart from the context and the state. -/
theorem fin_out {s₀ s : State} {m₀ : Mem} {rs : List Region} (hf₀ : Frame rs s₀.mem m₀)
    (hdc : ∀ r ∈ rs, (⟨s₀.gpr .r3, 256⟩ : Region).Disjoint r)
    (hds : ∀ r ∈ rs, (⟨s₀.gpr .r4, 80⟩ : Region).Disjoint r)
    {V : Reg → BitVec 64} {sp : Addr} (h29 : V .r29 = s₀.gpr .r3) (h30 : V .r30 = s₀.gpr .r4)
    (h22 : V .r22 = s₀.gpr .r5) {o : Nat} {iv a ct : List Byte}
    (hf : FinOut V sp o (ctxH s₀.mem (s₀.gpr .r3)) a ct m₀ s)
    (hs : StreamRepr s₀.mem (s₀.gpr .r4) (ctxCiph s₀.mem (s₀.gpr .r3))
      (ctxH s₀.mem (s₀.gpr .r3)) iv a ct) (hl : s₀.gpr .r5 = BitVec.ofNat 64 a.length) :
    bytesAt s.mem (V .r31 + BitVec.ofNat 64 o) 16 =
      fullTag (ctxCiph s₀.mem (s₀.gpr .r3)) (ctxH s₀.mem (s₀.gpr .r3)) iv a ct := by
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, -⟩ := hs
  have hb := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
  have dS : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ rs, (⟨s₀.gpr .r4 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hd r hr => (hds r hr).sub_left (Lay.stSub hd)
  have hab₀ : Absorbed m₀ (V .r30 + BitVec.ofNat 64 16) (V .r30 + BitVec.ofNat 64 32)
      (ctxH s₀.mem (s₀.gpr .r3)) (ghashInput a ct) := by
    rw [h30]
    exact hab.congr (blockAt_frame hf₀ (dS (d := 16) (by decide)))
      (bytesAt_frame hf₀ (dS (d := 32) (k := (ghashInput a ct).length % 16) (by omega_using [])) (by omega_using []))
  rw [hf.out hab₀,
    h29, ciph_keep hf₀ hdc, h30,
    blockAt_frame hf₀ (by simpa using dS (d := 0) (k := 16) (by decide)), hj,
    h22, toNat_of_eq hl, lensBlock_mod, Proof.Gcm.fullTag_eq]

theorem streamFinish_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] {s₀ : State} (h : streamFinishPPC64LE.pre s₀) :
    WP isa streamFinish s₀ fun s' => abiPreserved s₀ s' ∧ streamFinishPPC64LE.post s₀ s' := by
  have h' : finPre s₀ := h
  have L₀ := finLay h'
  have X₀ := finX h'
  have hh := h'
  obtain ⟨-, hwr, -, -, -, -, -, dtw, -, -, -, -, -⟩ := hh
  have hTw : Covers [⟨s₀.gpr .r7, 16⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have run : ∀ {a ct : List Byte}, a.length % 16 = (s₀.gpr .r5).toNat % 16 → (s₀.gpr .r6).toNat = ct.length →
      WP isa streamFinish s₀ fun s' => abiPreserved s₀ s' ∧ ∀ iv,
        StreamRepr s₀.mem (s₀.gpr .r4) (ctxCiph s₀.mem (s₀.gpr .r3))
          (ctxH s₀.mem (s₀.gpr .r3)) iv a ct → s₀.gpr .r5 = BitVec.ofNat 64 a.length →
        bytesAt s'.mem (s₀.gpr .r7) 16 =
          fullTag (ctxCiph s₀.mem (s₀.gpr .r3)) (ctxH s₀.mem (s₀.gpr .r3)) iv a ct := by
    intro a ct ha hP
    refine WP.seq (WP.mono (fin1_wp (fin_W h')) fun s₁ h1 => ?_)
    have he₁ := fin_env h' h1
    have L := L₀.v h1.r29 h1.r30 h1.r31
    have hH₁ : blockAt s₁.mem (s₁.gpr .r29 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .r3) := by
      rw [h1.r29]; exact ctxH_keep h1.en.frame (ctx_saved L₀)
    have X : XOk (s₁.gpr .r29) (s₁.gpr .r30) (s₁.gpr .r31) (s₁.gpr .r28) := by rw [h1.r29, h1.r30, h1.r31, h1.r28]; exact X₀
    refine WP.seq (WP.mono (WP.with_rdwr (finTag_ok L X (o := 0) (.inl rfl) (a := a) (ct := ct) he₁
      (by rw [h1.r28, h1.en.keeps.wr]; exact fin_X h') hH₁ (by rw [h1.r22]; exact ha)
      (by rw [h1.r23]; exact hP))) fun s₂ ⟨hf, rd₂, wr₂, _⟩ => ?_)
    have hTw₂ : Covers [⟨s₁.gpr .r20, 16⟩] s₂.wr := by
      rw [wr₂, h1.en.keeps.wr, h1.r20]; exact hTw
    have hTd : (⟨s₁.gpr .r20, 16⟩ : Region).Disjoint ⟨s₁.gpr .r31, 16⟩ := by
      rw [h1.r20, h1.r31]; exact dtw.sub_right (Region.sub_prefix (by decide))
    refine WP.seq (WP.mono (tagOut_ok hf.env hTw₂ hTd) fun s₃ ⟨hb₃, hf₃, g₃, hk₃⟩ => ?_)
    have he₃ := hf.env.keep (fun r hr => g₃ r (by revert r; decide)) hk₃.sp hk₃.rd hk₃.wr
    have sv₂ : SavedAt s₂.mem (s₀.gpr .r8) s₀ := by
      have := hf.frame; rw [h1.r30, h1.r31, h1.r28] at this
      exact h1.en.saved.frame this (saved_tagFrame L₀ X₀ (.inl rfl))
    have sv₃ : SavedAt s₃.mem (s₀.gpr .r8) s₀ := sv₂.frame hf₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h1.r20]
      exact (dtw.sub_right (VG.Offset.sub_base _ (show 128 + 120 ≤ scrBytes by decide))).symm)
    have e31 : s₃.gpr .r31 = s₀.gpr .r8 := (he₃.fr _ (by decide)).trans h1.r31
    refine WP.mono (restore_ok e31 (by have := he₃.perm.w; rw [h1.r31] at this; exact Covers.right this) sv₃
      he₃.sp (fun r hr => by rw [he₃.fr r (by revert hr; revert r; decide)]; exact h1.en.low r hr))
      fun s' ⟨ga, hm, _⟩ => ⟨ga, fun iv hs hl => ?_⟩
    have := fin_out (s := s₂) h1.en.frame (ctx_saved L₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using (L₀.saved_st (d := 0) (k := 80) (by decide)).symm) h1.r29 h1.r30
      h1.r22 hf hs hl
    rw [BitVec.add_zero] at this
    rw [hm, ← h1.r20, hb₃, this]
  have h₀ := run (a := List.replicate ((s₀.gpr .r5).toNat % 16) 0) (ct := List.replicate (s₀.gpr .r6).toNat 0)
    (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      StreamRepr s₀.mem (s₀.gpr .r4) (ctxCiph s₀.mem (s₀.gpr .r3))
          (ctxH s₀.mem (s₀.gpr .r3)) i.1 i.2.1 i.2.2 ∧
        s₀.gpr .r5 = BitVec.ofNat 64 i.2.1.length ∧ (s₀.gpr .r6).toNat = i.2.2.length)
    fun i hi => WP.mono (run (a := i.2.1) (ct := i.2.2) (by rw [hi.2.1, toNat_mod16]) hi.2.2)
      fun s' hh => hh.2 i.1 hi.1 hi.2.1)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => hh.2 ⟨iv, a, c⟩ ⟨hs, hl, hp⟩⟩

end VG.Proof.Sm4Gcm.PPC64LE

end

end

/-! ### `Sm4Gcm.PPC64LE.InitCT`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.PPC64LE.Init`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on PPC64LE: `vg_sm4_gcm_init`

Untrusted: everything here is checked by Lean. As AES-GCM's `init`
(`Proof/AesGcm/PPC64LE/Init.lean`): `init` saves our caller's registers in
`scratch` (`W`), expands the key into the context with SM4's key expansion,
inlined, and computes the hash subkey `CIPH_K(0¹²⁸)` into its bytes 240–255
with SM4's counter mode on a zero block, from a zero counter block at
`W + 96` (`init_wp`). SM4's working space is the argument after `W` (`r6`), kept in `r28`.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov tO)
open VG.Proof.AesGcm.PPC64LE (Keeps' SavedAt savedR save_ok restore_ok covers_mem covers_prefix covers_off
  in_off bytesAt_frame blockAt_frame blocksAt_one ctr32_single zero_block2 ctxH_eq write_8 saved_w
  length_bytesAt)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt)
open VG.Spec.Sm4.Gcm (KeyRepr)

/-- After the entry, from `s₀`. -/
structure IS1 (s₀ s₁ : State) : Prop where
  r31 : s₁.gpr .r31 = s₀.gpr .r5
  r29 : s₁.gpr .r29 = s₀.gpr .r4
  r5 : s₁.gpr .r5 = s₀.gpr .r6
  r28 : s₁.gpr .r28 = s₀.gpr .r6
  r3 : s₁.gpr .r3 = s₀.gpr .r3
  r4 : s₁.gpr .r4 = s₀.gpr .r4
  low : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17], s₁.gpr r = s₀.gpr r
  keeps : Keeps' s₀ s₁
  saved : SavedAt s₁.mem (s₀.gpr .r5) s₀
  frame : Frame [savedR (s₀.gpr .r5)] s₀.mem s₁.mem

theorem is1_wp {s₀ : State} (h : initPPC64LE.pre s₀) : WP isa (.block initPre) s₀ (IS1 s₀) := by
  obtain ⟨-, hwr, -, -, -, -, -, -⟩ := h
  obtain hW : Covers [⟨s₀.gpr .r5, 288⟩] s₀.wr := by
    rw [hwr]; exact covers_prefix (covers_mem (r := ⟨s₀.gpr .r5, scrBytes⟩) (by simp)) (by decide)
  refine WP.block_append (WP.mono (save_ok (b := .r5) (by decide) hW) fun s ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  obtain e4 : s.gpr .r4 = s₀.gpr .r4 := hg _ (by decide) (by decide)
  obtain e6 : s.gpr .r6 = s₀.gpr .r6 := hg _ (by decide) (by decide)
  crun [mov, BitVec.or_self, e4, e6, h31]
  exact ⟨by simp [h31], by simp, by simp, by simp, by simp [hg], by simp [hg],
    fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [hg],
    ⟨hk.rd, hk.wr, hk.sp, hk.lr⟩, hsv, hf⟩

theorem init_kc {s₀ s₁ : State} (h : initPPC64LE.pre s₀) (h1 : IS1 s₀ s₁) :
    KeyCall s₁ (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r6) := by
  obtain ⟨hrd, hwr, dkc, -, -, fk, fc, -, dkx, dcx, -, fx⟩ := h
  obtain hX : Covers [⟨s₀.gpr .r6, xBytes⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hC : Covers [⟨s₀.gpr .r4, 256⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  refine ⟨h1.r3, h1.r4, h1.r5, dkc.sub_right (Region.sub_prefix (by decide)),
    dkx.sub_right (Region.sub_prefix (by decide)),
    (dcx.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)), fk,
    by omega_using [fc], by simp only [xBytes, kBytes] at fx ⊢; omega_using [fx], ?_, ?_⟩
  · rw [h1.keeps.rd, h1.keeps.wr, hrd]
    exact Covers.cons (Covers.left (covers_mem (by simp))) (Covers.cons
      (Covers.right (covers_prefix hC (by decide))) (Covers.cons (Covers.right (covers_prefix hX
        (by decide))) Covers.nil))
  · rw [h1.keeps.wr]
    exact Covers.cons (covers_prefix hC (by decide)) (Covers.cons (covers_prefix hX (by decide))
      Covers.nil)

/-- `initArgs`: the hash subkey's block and `T` zeroed, and the arguments of
SM4's counter mode. -/
theorem initArgs_ok {C W X : Addr} {s : State} (h29 : s.gpr .r29 = C) (h31 : s.gpr .r31 = W)
    (h28 : s.gpr .r28 = X) (hc : Covers [⟨C, 256⟩] s.wr) (hw : Covers [⟨W, 288⟩] s.wr) :
    WP isa (.block initArgs) s fun s' =>
      s'.mem = (((s.mem.writeW (C + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
          (C + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 96)
          (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s'.gpr .r3 = C ∧ s'.gpr .r4 = W + BitVec.ofNat 64 96 ∧ s'.gpr .r5 = C + BitVec.ofNat 64 240 ∧
      s'.gpr .r6 = BitVec.ofNat 64 1 ∧ s'.gpr .r7 = X ∧
      (∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s'.gpr r = s.gpr r) ∧
      Keeps' s s' := by
  obtain c₀ := in_off hc (show 240 + 8 ≤ 256 by decide) (by decide)
  obtain c₁ := in_off hc (show 248 + 8 ≤ 256 by decide) (by decide)
  obtain w₀ := in_off hw (show 96 + 8 ≤ 288 by decide) (by decide)
  obtain w₁ := in_off hw (show 104 + 8 ≤ 288 by decide) (by decide)
  crun [initArgs, tO, h29, h31, h28, c₀, c₁, w₀, w₁, mov, BitVec.or_self, write_8]
  exact ⟨by simp only [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.reduceAdd],
    fun r a b c d e f => by simp [a, b, c, d, e, f], ⟨rfl, rfl, rfl, rfl⟩⟩

/-- The arguments of `init`'s counter mode: the hash subkey's block
encrypted from the counter block `T`. -/
theorem init_cc {C W X : Addr} {s : State} (dcs : (⟨C, 256⟩ : Region).Disjoint ⟨W, scrBytes⟩)
    (dcx : (⟨C, 256⟩ : Region).Disjoint ⟨X, xBytes⟩) (dsx : (⟨W, scrBytes⟩ : Region).Disjoint ⟨X, xBytes⟩)
    (fc : C.toNat + 256 ≤ 2 ^ 64) (fs : W.toNat + scrBytes ≤ 2 ^ 64) (fx : X.toNat + xBytes ≤ 2 ^ 64)
    (hW : Covers [⟨W, scrBytes⟩] s.wr) (hX : Covers [⟨X, xBytes⟩] s.wr)
    (hC : Covers [⟨C, 256⟩] s.wr) (a3 : s.gpr .r3 = C) (a4 : s.gpr .r4 = W + BitVec.ofNat 64 96)
    (a5 : s.gpr .r5 = C + BitVec.ofNat 64 240) (a6 : s.gpr .r6 = BitVec.ofNat 64 1)
    (a7 : s.gpr .r7 = X) :
    CtrCall s C (W + BitVec.ofNat 64 96) (C + BitVec.ofNat 64 240) X 1 := by
  have fs' : W.toNat + 288 ≤ 2 ^ 64 := fs
  refine ⟨a3, a4, a5, a6, a7, by decide, ?_, ?_, ?_, ?_, ?_, ?_, by omega_using [fc], ?_, ?_, fx, ?_, ?_⟩
  · exact (dcs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  · simpa using Offset.disjoint C (d := 0) (n := 128) (e := 240) (k := 16) (.inl (by decide))
      (by decide) (by decide)
  · exact dcx.sub_left (Region.sub_prefix (by decide))
  · exact ((dcs.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide))).symm
  · exact dsx.sub_left (Offset.sub_base _ (by decide))
  · exact dcx.sub_left (Offset.sub_base _ (by decide))
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 96) (by decide),
      Nat.mod_eq_of_lt (by omega_using [fs'])]; omega_using [fs']
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 240) (by decide),
      Nat.mod_eq_of_lt (by omega_using [fc])]; omega_using [fc]
  · exact Covers.cons (Covers.right (covers_prefix hC (by decide))) (Covers.cons
      (Covers.right (covers_off hW (by decide) (by decide))) (Covers.cons
        (Covers.right (covers_off hC (by decide) (by decide))) (Covers.cons
          (Covers.right hX) Covers.nil)))
  · exact Covers.cons (covers_off hW (by decide) (by decide)) (Covers.cons
      (covers_off hC (by decide) (by decide)) (Covers.cons hX Covers.nil))

/-- `init`. -/
theorem init_wp {s₀ : State} (h : initPPC64LE.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ initPPC64LE.post s₀ s' := by
  have h' := h
  obtain ⟨hrd, hwr, dkc, dks, dcs, fk, fc, fs, dkx, dcx, dsx, fx⟩ := h'
  have fs' : (s₀.gpr .r5).toNat + 288 ≤ 2 ^ 64 := fs
  obtain hW : Covers [⟨s₀.gpr .r5, scrBytes⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hX : Covers [⟨s₀.gpr .r6, xBytes⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hW' : Covers [⟨s₀.gpr .r5, 288⟩] s₀.wr := covers_prefix hW (by decide)
  obtain hC : Covers [⟨s₀.gpr .r4, 256⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  -- Regions apart from the saved slots, and from the key schedule.
  obtain sW : ∀ {d k : Nat}, d + k ≤ scrBytes → (d + k ≤ 128 ∨ 248 ≤ d) →
      (savedR (s₀.gpr .r5)).Disjoint ⟨s₀.gpr .r5 + BitVec.ofNat 64 d, k⟩ := fun h₁ h₂ =>
    Offset.disjoint _ (by omega_using [h₂]) (by decide) (by simp only [scrBytes] at h₁; omega_using [h₁])
  obtain sC : ∀ {d k : Nat}, d + k ≤ 256 → (savedR (s₀.gpr .r5)).Disjoint ⟨s₀.gpr .r4 + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ => ((dcs.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ (by decide))).symm
  obtain sC0 : (savedR (s₀.gpr .r5)).Disjoint ⟨s₀.gpr .r4, 128⟩ :=
    (dcs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide)) |>.symm
  obtain kW : ∀ {d k : Nat}, d + k ≤ scrBytes →
      (⟨s₀.gpr .r4, 128⟩ : Region).Disjoint ⟨s₀.gpr .r5 + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ => (dcs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ h₁)
  obtain kC : (⟨s₀.gpr .r4, 128⟩ : Region).Disjoint ⟨s₀.gpr .r4 + BitVec.ofNat 64 240, 16⟩ := by
    simpa using Offset.disjoint (s₀.gpr .r4) (d := 0) (n := 128) (e := 240) (k := 16)
      (.inl (by decide)) (by decide) (by decide)
  refine WP.seq (WP.mono (is1_wp h) fun s₁ h1 => ?_)
  refine WP.seq (WP.mono (key_wp (init_kc h h1)) fun s₂ kp => ?_)
  obtain g31 : s₂.gpr .r31 = s₀.gpr .r5 := (kp.saved _ (by decide)).trans h1.r31
  obtain g29 : s₂.gpr .r29 = s₀.gpr .r4 := (kp.saved _ (by decide)).trans h1.r29
  obtain g28 : s₂.gpr .r28 = s₀.gpr .r6 := (kp.saved _ (by decide)).trans h1.r28
  obtain wr₂ : s₂.wr = s₀.wr := kp.wr.trans h1.keeps.wr
  refine WP.seq (WP.mono (initArgs_ok g29 g31 g28 (by rw [wr₂]; exact hC) (by rw [wr₂]; exact hW'))
    fun s₃ ⟨hm₃, a3, a4, a5, a6, a7, hg₃, hk₃⟩ => ?_)
  obtain cc : CtrCall s₃ (s₀.gpr .r4) (s₀.gpr .r5 + BitVec.ofNat 64 96) (s₀.gpr .r4 + BitVec.ofNat 64 240)
      (s₀.gpr .r6) 1 :=
    init_cc dcs dcx dsx fc fs fx (by rw [hk₃.wr, wr₂]; exact hW) (by rw [hk₃.wr, wr₂]; exact hX)
      (by rw [hk₃.wr, wr₂]; exact hC) a3 a4 a5 a6 a7
  refine WP.seq (WP.mono (ctr_wp cc) fun s₄ cp => ?_)
  -- The memory along the way.
  obtain ⟨m₂', hm₂'⟩ : ∃ m, m = (s₂.mem.writeW (s₀.gpr .r4 + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
      (s₀.gpr .r4 + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64) := ⟨_, rfl⟩
  rw [← hm₂'] at hm₃
  obtain fa : Frame [⟨s₀.gpr .r4 + BitVec.ofNat 64 240, 16⟩] s₂.mem m₂' := by
    rw [hm₂']; exact Proof.Cmac.frame_store2 _ _ _
  obtain fb : Frame [⟨s₀.gpr .r5 + BitVec.ofNat 64 96, 16⟩] m₂' s₃.mem := by
    rw [hm₃]; exact Proof.Cmac.frame_store2 _ _ _
  obtain f₃ : Frame [⟨s₀.gpr .r4 + BitVec.ofNat 64 240, 16⟩, ⟨s₀.gpr .r5 + BitVec.ofNat 64 96, 16⟩]
      s₂.mem s₃.mem :=
    (fa.mono (by simp)).trans (fb.mono (by simp))
  obtain sv₄ : SavedAt s₄.mem (s₀.gpr .r5) s₀ := by
    refine ((h1.saved.frame kp.frame ?_).frame f₃ ?_).frame cp.frame ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sC0
      · exact (dsx.sub_left (Offset.sub_base _ (by decide))).sub_right (Region.sub_prefix (by decide))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sC (by decide)
      · exact sW (by decide) (.inl (by decide))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sW (by decide) (.inl (by decide))
      · simpa using sC (d := 240) (k := 16) (by decide)
      · exact dsx.sub_left (Offset.sub_base _ (by decide))
  obtain hk₄ : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17], s₄.gpr r = s₀.gpr r := fun r hr => by
    rw [cp.saved r (by revert hr; revert r; decide), hg₃ r (by revert hr; revert r; decide)
      (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
      (by revert hr; revert r; decide) (by revert hr; revert r; decide),
      kp.saved r (by revert hr; revert r; decide), h1.low r hr]
  refine WP.mono (restore_ok (s₀ := s₀) (by rw [cp.saved _ (by decide), hg₃ _ (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), g31])
    (by rw [cp.rd, cp.wr, hk₃.rd, hk₃.wr, wr₂]; exact Covers.right hW') sv₄
    (by rw [cp.sp, hk₃.sp, kp.sp, h1.keeps.sp])
    hk₄) fun s' ⟨hab, hm', _, _, _⟩ => ⟨hab, ?_⟩
  -- The key schedule and the hash subkey.
  obtain key₁ : Spec.Sm4.blockAt s₁.mem (s₀.gpr .r3) =
      Vector.ofFn fun i => (bytesAt s₀.mem (s₀.gpr .r3) 16).getD i.val 0 := by
    rw [← Proof.Sm4.ofFn_toList (Spec.Sm4.blockAt s₁.mem _), ← Proof.Sm4.bytesAt_eq_blockAt,
      bytesAt_frame h1.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dks.sub_right (Offset.sub_base _ (by decide))) (by decide)]
  obtain ks₃ : Spec.Sm4.scheduleAt s₃.mem (s₀.gpr .r4) =
      Spec.Sm4.expandKey (Vector.ofFn fun i => (bytesAt s₀.mem (s₀.gpr .r3) 16).getD i.val 0) := by
    rw [Proof.Sm4.scheduleAt_frame f₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact kC
        · exact kW (by decide)), kp.out, key₁]
  simp only [initPPC64LE, KeyRepr, hm']
  refine ⟨?_, ?_⟩
  · rw [Proof.Sm4.scheduleAt_frame cp.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact kW (by decide)
        · simpa using kC
        · exact dcx.sub_left (Region.sub_prefix (by decide))), ks₃]
  · have cout := cp.out
    rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq] at cout
    obtain z₁ : blockAt s₃.mem (s₀.gpr .r5 + BitVec.ofNat 64 96) = 0 := by rw [hm₃, zero_block2]
    obtain z₂ : blockAt s₃.mem (s₀.gpr .r4 + BitVec.ofNat 64 240) = 0 := by
      rw [blockAt_frame fb (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dcs.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide))),
        hm₂', zero_block2]
    rw [ctxH_eq, cout.1, z₁, z₂]
    refine BitVec.zero_xor.trans ?_
    simp only [Spec.Sm4.gcmCipherOfKey, ks₃]

end VG.Proof.Sm4Gcm.PPC64LE

end

end

/-! ### `Sm4Gcm.PPC64LE.CTCrypt`, which the modules that import this one used -/

section

/-!
# SM4-GCM on PPC64LE: `crypt` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/CTFin.lean`): the invariants fix the context, the
state, `W`, the stack pointer, the data's address and length, and the length
of the text so far modulo 16; SM4's counter mode is constant time by its own
proof (`CT.ctr`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov cryptFill splitWhole xorLoop)
open VG.Proof.AesGcm.PPC64LE (CT Env Lay DataW eval_zero split_ok)

/-- Before `crypt`. -/
def CrI (c st w x sp : Addr) (D : Addr) (n q : Nat) (s : State) : Prop :=
  ∃ V icb P, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧ P % 16 = q ∧ CrIn V sp icb P D n s

/-- Part of the way: `j` bytes done. -/
def CrM (c st w x sp : Addr) (D : Addr) (n q j : Nat) (s : State) : Prop :=
  ∃ V icb P m₀, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧ P % 16 = q ∧ CrMid V sp icb P D n m₀ j s

/-- Environments that agree on `r28` to `r31` agree in those registers. -/
theorem pinK {V₁ V₂ : Reg → BitVec 64} {sp : Addr} {s₁ s₂ : State} (e₁ : Env V₁ sp s₁) (e₂ : Env V₂ sp s₂)
    (h29 : V₁ .r29 = V₂ .r29) (h30 : V₁ .r30 = V₂ .r30) (h31 : V₁ .r31 = V₂ .r31) (h28 : V₁ .r28 = V₂ .r28)
    {r : Reg} (hr : r ∈ [Reg.r28, .r29, .r30, .r31]) : s₁.gpr r = s₂.gpr r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), h28]
  · rw [e₁.r29, e₂.r29, h29]
  · rw [e₁.r30, e₂.r30, h30]
  · rw [e₁.r31, e₂.r31, h31]

section
variable {c st w x sp : Addr} (L : Lay c st w) (X : XOk c st w x)
include L X

theorem cryptWhole_ct {D : Addr} {n q j : Nat} :
    CT (CrM c st w x sp D n q j) cryptWhole := by
  obtain ⟨nb, hnb⟩ : ∃ nb, nb = (n - j) / 16 := ⟨_, rfl⟩
  let J₁ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧
    Env V sp s ∧ DataW (V .r29) (V .r30) (V .r31) s D n ∧ j ≤ n ∧ Covers [xR (V .r28)] s.wr ∧
    (⟨D, n⟩ : Region).Disjoint (xR (V .r28)) ∧
    s.gpr .r5 = D + BitVec.ofNat 64 j ∧ s.gpr .r6 = BitVec.ofNat 64 nb
  refine CT.seq (J := J₁) ?_ (fun s ⟨V, icb, P, m₀, h29, h30, h31, h28, hP, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r24, .r25]) (.block splitWhole)
        h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, _, _, _, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.r24, h₂.r24]
    · rw [h₁.r25, h₂.r25]
  · refine WP.mono (split_ok hs.le hs.data.ok.lt hs.r24 hs.r25) fun s₁ ⟨h5, h6, _, _, hg₁, hk₁⟩ => ?_
    exact ⟨V, h29, h30, h31, h28, hs.env.keep (fun r hr => hg₁ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr, hs.data.of_eq hk₁.rd hk₁.wr, hs.le,
      by rw [hk₁.wr]; exact hs.xw, hs.dx, h5, by rw [h6, hnb]⟩
  · refine CT.ite (decide (nb = 0)) (fun s ⟨_, _, _, _, _, _, hd, _, _, _, _, h6⟩ =>
      eval_zero h6 (by have := hd.ok.lt; omega_using [hnb, this])) (fun _ => CT.skip) fun hb => ?_
    have h0 : nb ≠ 0 := by simpa using hb
    let J₂ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧
      Env V sp s ∧ DataW (V .r29) (V .r30) (V .r31) s D n ∧ j ≤ n ∧ Covers [xR (V .r28)] s.wr ∧
      (⟨D, n⟩ : Region).Disjoint (xR (V .r28)) ∧
      s.gpr .r3 = V .r29 ∧ s.gpr .r4 = V .r30 + BitVec.ofNat 64 48 ∧
      s.gpr .r5 = D + BitVec.ofNat 64 j ∧ s.gpr .r6 = BitVec.ofNat 64 nb ∧
      s.gpr .r7 = V .r28
    refine CT.seq (J := J₂) ?_ (fun s ⟨V, h29, h30, h31, h28, he, hd, hj, hxw, hdx, h5, h6⟩ => ?_) ?_
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28, .r29, .r30, .r31])
          (.block (ctrArgs 48)) h).isSome = true := ⟨_, by taint_decide⟩
      exact CT.taint _ (fun s₁ s₂ ⟨_, a29, a30, a31, a28, e₁, _⟩ ⟨_, b29, b30, b31, b28, e₂, _⟩ =>
        ⟨e₁.sp.trans e₂.sp.symm, fun r hr => pinK e₁ e₂ (a29.trans b29.symm)
          (a30.trans b30.symm) (a31.trans b31.symm) (a28.trans b28.symm) hr⟩) hc
    · refine WP.mono (ctrArgs_ok he) fun s₂ ⟨a3, a4, a7, hg₂, hk₂⟩ => ?_
      exact ⟨V, h29, h30, h31, h28, he.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
        (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr, hd.of_eq hk₂.rd hk₂.wr, hj, by rw [hk₂.wr]; exact hxw, hdx,
        a3, a4, by rw [hg₂ _ (by decide) (by decide) (by decide), h5],
        by rw [hg₂ _ (by decide) (by decide) (by decide), h6], a7⟩
    · refine CT.ctr fun s₁ s₂ ⟨V₁, a29, a30, a31, a28, he₁, hd₁, hj₁, ax, adx, a3, a4, a5, a6, a7⟩
        ⟨V₂, b29, b30, b31, b28, he₂, hd₂, _, bx, bdx, b3, b4, b5, b6, b7⟩ => ?_
      have hn₁ := hd₁.ok.lt
      have g₁ := ctrWhole_mk (L.v a29 a30 a31) (by rw [a29, a30, a31, a28]; exact X) he₁ a3 a4 a5 a6 a7 (by omega_using [hnb, hn₁])
        (hd₁.sub (j := j) (k := 16 * nb) (by omega_using [hnb, h0]) (by omega_using [h0])) ax (adx.sub_left (VG.Offset.sub_base _ (by omega_using [hnb, h0])))
      have g₂ := ctrWhole_mk (L.v b29 b30 b31) (by rw [b29, b30, b31, b28]; exact X) he₂ b3 b4 b5 b6 b7 (by omega_using [hnb, hn₁])
        (hd₂.sub (j := j) (k := 16 * nb) (by omega_using [hnb, h0]) (by omega_using [h0])) bx (bdx.sub_left (VG.Offset.sub_base _ (by omega_using [hnb, h0])))
      rw [a29, a30, a28] at g₁
      rw [b29, b30, b28] at g₂
      exact ⟨_, _, _, _, _, g₁, g₂, he₁.sp.trans he₂.sp.symm⟩

theorem cryptTail_ct {D : Addr} {n q j : Nat} :
    CT (CrM c st w x sp D n q j) cryptTail := by
  refine CT.ite (decide (n - j = 0)) (fun s ⟨_, _, _, _, _, _, _, _, _, hs⟩ =>
    eval_zero hs.r25 (by have := hs.data.ok.lt; omega_using [this])) (fun _ => CT.skip) fun _ => ?_
  let J₁ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧
    Env V sp s ∧ Covers [xR (V .r28)] s.wr ∧ s.gpr .r3 = V .r29 ∧
    s.gpr .r4 = V .r30 + BitVec.ofNat 64 48 ∧ s.gpr .r5 = V .r30 + BitVec.ofNat 64 64 ∧
    s.gpr .r6 = BitVec.ofNat 64 1 ∧ s.gpr .r7 = V .r28
  let J₂ : State → Prop := fun s => ∃ V icb P m₀ s₀, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧
    TailKs V sp icb P D n m₀ j s₀ s
  refine CT.seq (J := J₂) (CT.seq (J := J₁) ?_ (fun s ⟨V, icb, P, m₀, h29, h30, h31, h28, hP, hs⟩ => ?_) ?_)
    (fun s ⟨V, icb, P, m₀, h29, h30, h31, h28, hP, hs⟩ =>
      WP.mono (tailKs_ok (L.v h29 h30 h31) (by rw [h29, h30, h31, h28]; exact X) hs) fun s' h =>
        ⟨V, icb, P, m₀, s, h29, h30, h31, h28, h⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28, .r29, .r30, .r31])
        (.block tailArgs) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a29, a30, a31, a28, _, h₁⟩ ⟨_, _, _, _, b29, b30, b31, b28, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => pinK h₁.env h₂.env
        (a29.trans b29.symm) (a30.trans b30.symm) (a31.trans b31.symm) (a28.trans b28.symm) hr⟩) hc
  · refine WP.mono (tailArgs_ok hs.env) fun s₂ ⟨_, a3, a4, a5, a6, a7, hg₂, hk₂⟩ => ?_
    exact ⟨V, h29, h30, h31, h28, hs.env.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)) hk₂.sp hk₂.rd
      hk₂.wr, by rw [hk₂.wr]; exact hs.xw, a3, a4, a5, a6, a7⟩
  · exact CT.ctr fun s₁ s₂ ⟨V₁, a29, a30, a31, a28, he₁, ax, a3, a4, a5, a6, a7⟩
      ⟨V₂, b29, b30, b31, b28, he₂, bx, b3, b4, b5, b6, b7⟩ => by
      have g₁ := ctrTail_mk (L.v a29 a30 a31) (by rw [a29, a30, a31, a28]; exact X) he₁ a3 a4 a5 a6 a7 ax
      have g₂ := ctrTail_mk (L.v b29 b30 b31) (by rw [b29, b30, b31, b28]; exact X) he₂ b3 b4 b5 b6 b7 bx
      rw [a29, a30, a28] at g₁
      rw [b29, b30, b28] at g₂
      exact ⟨_, _, _, _, _, g₁, g₂, he₁.sp.trans he₂.sp.symm⟩
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r24, .r25, .r30])
        (.seq (.block [.addi .r3 .r30 64, mov .r4 .r24, mov .r5 .r25]) xorLoop) h).isSome = true :=
      ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, a30, _, _, h₁⟩ ⟨_, _, _, _, _, _, b30, _, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.r24, h₂.r24]
    · rw [h₁.r25, h₂.r25]
    · rw [h₁.env.r30, h₂.env.r30, a30, b30]

theorem crypt_ct {D : Addr} {n q : Nat} :
    CT (CrI c st w x sp D n q) crypt := by
  refine CT.ite (decide (n = 0)) (fun s ⟨_, _, _, _, _, _, _, _, hs⟩ => eval_zero hs.r25 hs.data.ok.lt)
    (fun _ => CT.skip) fun hb => ?_
  have h0 : n ≠ 0 := by simpa using hb
  let j₁ := if q = 0 then 0 else min (16 - q) n
  refine CT.seq (J := CrM c st w x sp D n q j₁) ?_
    (fun s ⟨V, icb, P, h29, h30, h31, h28, hP, hs⟩ => WP.mono (cryptFill_ok hs h0) fun s' ⟨j, hj, hm⟩ =>
      ⟨V, icb, P, s.mem, h29, h30, h31, h28, hP, by subst hj; rw [hP] at hm; exact hm⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r24, .r25, .r26, .r30]) cryptFill
        h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a30, _, _, hP₁, h₁⟩ ⟨_, _, _, _, b30, _, _, hP₂, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.r24, h₂.r24]
    · rw [h₁.r25, h₂.r25]
    · rw [h₁.r26, h₂.r26, hP₁, hP₂]
    · rw [h₁.env.r30, h₂.env.r30, a30, b30]
  refine CT.seq (J := CrM c st w x sp D n q (j₁ + 16 * ((n - j₁) / 16))) (cryptWhole_ct L X)
    (fun s ⟨V, icb, P, m₀, h29, h30, h31, h28, hP, hs⟩ =>
      WP.mono (cryptWhole_ok (L.v h29 h30 h31) (by rw [h29, h30, h31, h28]; exact X) hs) fun s' ⟨j, hj, hm, _⟩ =>
        ⟨V, icb, P, m₀, h29, h30, h31, h28, hP, by subst hj; exact hm⟩) (cryptTail_ct L X)

end

end VG.Proof.Sm4Gcm.PPC64LE

end

end

/-!
# SM4-GCM on PPC64LE: `vg_sm4_gcm_init` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/CTFin.lean`): the code around SM4's inlined code by
the taint analysis, from the public arguments and the registers the
correctness proof pins; SM4's code by its own proofs (`CT.key`, `CT.ctr`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (restore)
open VG.Proof.AesGcm.PPC64LE (CT ct_of CT.taintEq covers_mem covers_prefix)

theorem initPre_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (.block initPre) h).isSome = true := ⟨_, by taint_decide⟩

theorem initArgs_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28, .r29, .r31])
    (.block initArgs) h).isSome = true := ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r31])
    (.block restore) h).isSome = true := ⟨_, by taint_decide⟩

theorem init_ct : ConstantTime isa initPPC64LE.pre initPPC64LE.pub init := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, qsp⟩ := hq
  have hpre₁ := h₁
  obtain ⟨-, -, -, -, dcs, -, fc, fs, -, dcx, dsx, fx⟩ := hpre₁
  generalize hK : σ₁.gpr .r3 = K at *
  generalize hC : σ₁.gpr .r4 = C at *
  generalize hW : σ₁.gpr .r5 = W at *
  generalize hX : σ₁.gpr .r6 = X at *
  generalize hSP : σ₁.sp = SP at *
  let I₀ : State → Prop := fun s => initPPC64LE.pre s ∧ s.gpr .r3 = K ∧ s.gpr .r4 = C ∧ s.gpr .r5 = W ∧
    s.gpr .r6 = X ∧ s.sp = SP
  let I₁ : State → Prop := fun s => KeyCall s K C X ∧
    s.gpr .r29 = C ∧ s.gpr .r31 = W ∧ s.gpr .r28 = X ∧ s.sp = SP ∧
    s.wr = [⟨C, 256⟩, ⟨W, scrBytes⟩, ⟨X, xBytes⟩]
  let I₂ : State → Prop := fun s => s.gpr .r29 = C ∧ s.gpr .r31 = W ∧ s.gpr .r28 = X ∧
    s.sp = SP ∧ s.wr = [⟨C, 256⟩, ⟨W, scrBytes⟩, ⟨X, xBytes⟩]
  let I₃ : State → Prop := fun s => CtrCall s C (W + BitVec.ofNat 64 96) (C + BitVec.ofNat 64 240)
    X 1 ∧ s.gpr .r31 = W ∧ s.sp = SP
  let I₄ : State → Prop := fun s => s.gpr .r31 = W ∧ s.sp = SP
  refine ⟨I₀, ⟨h₁, hK, hC, hW, hX, hSP⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, qsp.symm⟩, ?_⟩
  refine CT.seq (J := I₁) ?_ (fun s ⟨hs, e3, e4, e5, e6, esp⟩ => WP.mono (is1_wp hs) fun s₁ h1 => ?_) ?_
  · obtain ⟨_, hc⟩ := initPre_taint
    exact CT.taintEq (I := I₀) _
      (fun r => if r = .r3 then K else if r = .r4 then C else if r = .r5 then W else X) SP
      (fun s ⟨_, e3, e4, e5, e6, esp⟩ => ⟨esp, by simp [e3, e4, e5, e6]⟩) hc
  · have kc := init_kc hs h1
    rw [e3, e4, e6] at kc
    obtain ⟨-, hwr, -⟩ := hs
    refine ⟨kc, by rw [h1.r29, e4], by rw [h1.r31, e5], by rw [h1.r28, e6],
      by rw [h1.keeps.sp, esp], by rw [h1.keeps.wr, hwr, e4, e5, e6]⟩
  refine CT.seq (J := I₂) ?_ (fun s ⟨kc, e29, e31, e28, esp, ewr⟩ => WP.mono (key_wp kc) fun s₂ kp =>
    ⟨by rw [kp.saved _ (by decide), e29], by rw [kp.saved _ (by decide), e31],
      by rw [kp.saved _ (by decide), e28], by rw [kp.sp, esp], by rw [kp.wr, ewr]⟩) ?_
  · exact CT.key fun s₁ s₂ h₁ h₂ => ⟨_, _, _, h₁.1, h₂.1, h₁.2.2.2.2.1.trans h₂.2.2.2.2.1.symm⟩
  refine CT.seq (J := I₃) ?_ (fun s ⟨e29, e31, e28, esp, ewr⟩ =>
    WP.mono (initArgs_ok e29 e31 e28 (by rw [ewr]; exact covers_mem (by simp))
      (by rw [ewr]; exact covers_mem (r := ⟨W, scrBytes⟩) (by simp)))
      fun s₃ ⟨_, a3, a4, a5, a6, a7, hg₃, hk₃⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := initArgs_taint
    exact CT.taintEq (I := I₂) _ (fun r => if r = .r28 then X else if r = .r29 then C else W)
      SP (fun s ⟨e29, e31, e28, esp, _⟩ => ⟨esp, by simp [e29, e31, e28]⟩) hc
  · have hW₃ : Covers [⟨W, scrBytes⟩] s₃.wr := by rw [hk₃.wr, ewr]; exact covers_mem (by simp)
    have hX₃ : Covers [⟨X, xBytes⟩] s₃.wr := by rw [hk₃.wr, ewr]; exact covers_mem (by simp)
    have hC₃ : Covers [⟨C, 256⟩] s₃.wr := by rw [hk₃.wr, ewr]; exact covers_mem (by simp)
    exact ⟨init_cc dcs dcx dsx fc fs fx hW₃ hX₃ hC₃ a3 a4 a5 a6 a7,
      by rw [hg₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e31],
      by rw [hk₃.sp, esp]⟩
  refine CT.seq (J := I₄) ?_ (fun s ⟨cc, e31, esp⟩ => WP.mono (ctr_wp cc) fun s₄ cp =>
    ⟨by rw [cp.saved _ (by decide), e31], by rw [cp.sp, esp]⟩) ?_
  · exact CT.ctr fun s₁ s₂ h₁ h₂ => ⟨_, _, _, _, _, h₁.1, h₂.1, h₁.2.2.trans h₂.2.2.symm⟩
  · obtain ⟨_, hc⟩ := restore_taint
    exact CT.taintEq (I := I₄) _ (fun _ => W) SP (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.Sm4Gcm.PPC64LE

end

end

/-!
# SM4-GCM on PPC64LE: `tag`, `finTag` and `vg_sm4_gcm_stream_finish` are constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/CTFin.lean`): the invariants fix the context, the
state, `W`, the stack pointer, the lengths of the additional data (`r22`)
and of the text (`r23`), and the tag's address (`r20`), all held in
registers the environment pins, and the permission to write SM4's working
space.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov lens flush tagOut)
open VG.Proof.AesGcm.PPC64LE (CT ct_of CT.taintEq Env Lay Keeps covers_mem eval_zero and15 lens_ct lens_ok
  flush_ct flush_ok tagOut_ok finQ WP.with_rdwr)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- An environment that may write SM4's working space. -/
def EnvX (c st w x sp : Addr) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧ Env V sp s ∧ Covers [xR x] s.wr

/-- Before `finTag`: also `aad_len` (`A`) and `text_len` (`T`) in `r22` and `r23`. -/
def FTI (c st w x sp : Addr) (A T : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧ V .r22 = A ∧
    V .r23 = T ∧ Env V sp s ∧ Covers [xR x] s.wr

section
variable {c st w x sp : Addr} (L : Lay c st w) (X : XOk c st w x)
include L X

theorem tag_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] {o : Nat} (ho : o = 0 ∨ o = 112) :
    CT (EnvX c st w x sp) (tag o) := by
  refine CT.seq (J := EnvX c st w x sp)
    ((lens_ct L (yo := 16) (.inr rfl)).mono fun s ⟨V, a, b, d, _, he, _⟩ => ⟨V, a, b, d, he⟩)
    (fun s ⟨V, a, b, d, e, he, hx⟩ => WP.mono (WP.with_rdwr (lens_ok (L.v a b d) (.inr rfl) he rfl))
      fun s' ⟨h, _, wr, _⟩ => ⟨V, a, b, d, e, h.1, by rw [wr]; exact hx⟩) ?_
  let J : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧
    V .r28 = x ∧ Env V sp s ∧ Covers [xR x] s.wr ∧ s.gpr .r3 = V .r29 ∧ s.gpr .r4 = V .r30 ∧
    s.gpr .r5 = V .r31 + BitVec.ofNat 64 o ∧ s.gpr .r6 = BitVec.ofNat 64 1 ∧
    s.gpr .r7 = V .r28
  refine CT.seq (J := J) ?_ (fun s ⟨V, a, b, d, e, he, hx⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28, .r29, .r30, .r31])
        (.block (tagArgs o)) h).isSome = true := by rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, a₁, b₁, d₁, c₁, h₁, _⟩ ⟨_, a₂, b₂, d₂, c₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => pinK h₁ h₂ (a₁.trans a₂.symm)
        (b₁.trans b₂.symm) (d₁.trans d₂.symm) (c₁.trans c₂.symm) hr⟩) hc
  · refine WP.mono (tagArgs_ok (o := o) (by omega_using [ho]) (by omega_using [ho]) he)
      fun s' ⟨_, a3, a4, a5, a6, a7, hg, hk⟩ => ⟨V, a, b, d, e, he.keep (fun r hr => hg r (by revert r; decide)
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)) hk.sp hk.rd
        hk.wr, by rw [hk.wr]; exact hx, a3, a4, a5, a6, a7⟩
  · exact CT.ctr fun s₁ s₂ ⟨V₁, a₁, b₁, d₁, c₁, e₁, x₁, a3, a4, a5, a6, a7⟩
      ⟨V₂, a₂, b₂, d₂, c₂, e₂, x₂, b3, b4, b5, b6, b7⟩ => by
      have g₁ := ctrTag_mk (L.v a₁ b₁ d₁) (by rw [a₁, b₁, d₁, c₁]; exact X) ho e₁ a3 a4 a5 a6 a7
        (by rw [c₁]; exact x₁)
      have g₂ := ctrTag_mk (L.v a₂ b₂ d₂) (by rw [a₂, b₂, d₂, c₂]; exact X) ho e₂ b3 b4 b5 b6 b7
        (by rw [c₂]; exact x₂)
      rw [a₁, b₁, d₁, c₁] at g₁
      rw [a₂, b₂, d₂, c₂] at g₂
      exact ⟨_, _, _, _, _, g₁, g₂, e₁.sp.trans e₂.sp.symm⟩

theorem finTag_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] {o : Nat} (ho : o = 0 ∨ o = 112) {A T : BitVec 64} :
    CT (FTI c st w x sp A T) (finTag o) := by
  have hq : finQ A T < 16 := by simp only [finQ]; split <;> exact Nat.mod_lt _ (by decide)
  let J : State → Prop := fun s => FTI c st w x sp A T s ∧ s.gpr .r26 = BitVec.ofNat 64 (finQ A T)
  refine CT.seq (J := J) ?_ (fun s ⟨V, a, b, d, e, f, g, he, hx⟩ => ?_) ?_
  · refine CT.ite (decide (T.toNat = 0)) (fun s ⟨_, _, _, _, _, _, g, he, _⟩ =>
      eval_zero (by rw [he.ofNat (r := .r23) (by decide), g]) T.isLt) (fun _ => ?_) (fun _ => ?_)
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r22])
          (.block [.li .r0 15, .logic .and .r26 .r22 .r0]) h).isSome = true := ⟨_, by taint_decide⟩
      refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, f₁, _, h₁, _⟩ ⟨_, _, _, _, _, f₂, _, h₂, _⟩ =>
        ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
      simp only [List.mem_singleton] at hr; subst hr
      rw [h₁.fr _ (by decide), h₂.fr _ (by decide), f₁, f₂]
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r23])
          (.block [.li .r0 15, .logic .and .r26 .r23 .r0]) h).isSome = true := ⟨_, by taint_decide⟩
      refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, g₁, h₁, _⟩ ⟨_, _, _, _, _, _, g₂, h₂, _⟩ =>
        ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
      simp only [List.mem_singleton] at hr; subst hr
      rw [h₁.fr _ (by decide), h₂.fr _ (by decide), g₁, g₂]
  · have h22 := he.fr .r22 (by decide)
    have h23 := he.fr .r23 (by decide)
    refine WP.ite (decide (T.toNat = 0)) (eval_zero (by rw [he.ofNat (r := .r23) (by decide), g]) T.isLt)
      (fun ht => ?_) (fun hf => ?_)
    · have hand := and15 (V .r22)
      have hQ : finQ A T = (V .r22).toNat % 16 := by simp only [finQ, f]; simp at ht; simp [ht]
      have h₃ : WP isa (.block [.li .r0 15, .logic .and .r26 .r22 .r0]) s fun s₃ =>
          s₃.gpr .r26 = BitVec.ofNat 64 ((V .r22).toNat % 16) ∧
            (∀ r, r ≠ .r0 → r ≠ .r26 → s₃.gpr r = s.gpr r) ∧ Keeps s s₃ := by
        crun [h22, hand]
        exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      exact WP.mono h₃ fun s₃ ⟨h26, hg, hk⟩ => ⟨⟨V, a, b, d, e, f, g, he.keep (fun r hr => hg r
        (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr, by rw [hk.wr]; exact hx⟩, by rw [h26, hQ]⟩
    · have hand := and15 (V .r23)
      have hQ : finQ A T = (V .r23).toNat % 16 := by simp only [finQ, g]; simp at hf; simp [hf]
      have h₃ : WP isa (.block [.li .r0 15, .logic .and .r26 .r23 .r0]) s fun s₃ =>
          s₃.gpr .r26 = BitVec.ofNat 64 ((V .r23).toNat % 16) ∧
            (∀ r, r ≠ .r0 → r ≠ .r26 → s₃.gpr r = s.gpr r) ∧ Keeps s s₃ := by
        crun [h23, hand]
        exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      exact WP.mono h₃ fun s₃ ⟨h26, hg, hk⟩ => ⟨⟨V, a, b, d, e, f, g, he.keep (fun r hr => hg r
        (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr, by rw [hk.wr]; exact hx⟩, by rw [h26, hQ]⟩
  refine CT.seq (J := FTI c st w x sp A T)
    ((flush_ct L (yo := 16) (.inr rfl) hq).mono fun s ⟨⟨V, a, b, d, _, _, _, he, _⟩, h26⟩ => ⟨⟨V, a, b, d, he⟩, h26⟩)
    (fun s ⟨⟨V, a, b, d, e, f, g, he, hx⟩, h26⟩ => WP.mono (WP.with_rdwr (flush_ok (L.v a b d) (yo := 16) (.inr rfl)
      (x := List.replicate (finQ A T) 0) ⟨he, rfl⟩ (by simp [h26, Nat.mod_eq_of_lt hq]))) fun s' ⟨fl, _, wr, _⟩ =>
        ⟨V, a, b, d, e, f, g, fl.env, by rw [wr]; exact hx⟩) ?_
  refine CT.seq (J := EnvX c st w x sp) ?_ (fun s ⟨V, a, b, d, e, f, g, he, hx⟩ => ?_)
    ((tag_ct L X ho).mono fun _ h => h)
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r22, .r23])
        (.block [mov .r24 .r22, mov .r26 .r23]) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, f₁, g₁, h₁, _⟩ ⟨_, _, _, _, _, f₂, g₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), f₁, f₂]
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), g₁, g₂]
  · have h₅ : WP isa (.block [mov .r24 .r22, mov .r26 .r23]) s fun s₅ =>
        (∀ r, r ≠ .r24 → r ≠ .r26 → s₅.gpr r = s.gpr r) ∧ Keeps s s₅ := by
      crun [mov, BitVec.or_self]
      exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    exact WP.mono h₅ fun s₅ ⟨hg, hk⟩ => ⟨V, a, b, d, e, he.keep (fun r hr => hg r (by revert r; decide)
      (by revert r; decide)) hk.sp hk.rd hk.wr, by rw [hk.wr]; exact hx⟩

end

/-- In `finish`, after the entry: also the tag's address `Tp` in `r20`, which
the state may write. -/
def FinI (c st w x sp : Addr) (A T Tp : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧ V .r22 = A ∧
    V .r23 = T ∧ V .r20 = Tp ∧ Env V sp s ∧ Covers [⟨Tp, 16⟩] s.wr ∧ Covers [xR x] s.wr

theorem finEntry_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9]) (.block finEntry) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tagOut_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r20, .r31]) (.block tagOut)
    h).isSome = true := ⟨_, by taint_decide⟩

theorem streamFinish_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] : ConstantTime isa streamFinishPPC64LE.pre streamFinishPPC64LE.pub streamFinish := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, qsp⟩ := hq
  have h₁' : finPre σ₁ := h₁
  have L := finLay h₁'
  have X := finX h₁'
  have dtw : (⟨σ₁.gpr .r7, 16⟩ : Region).Disjoint ⟨σ₁.gpr .r8, 16⟩ :=
    h₁'.2.2.2.2.2.2.2.1.sub_right (Region.sub_prefix (by decide))
  let I₀ : State → Prop := fun s => finPre s ∧ s.gpr .r3 = σ₁.gpr .r3 ∧ s.gpr .r4 = σ₁.gpr .r4 ∧
    s.gpr .r5 = σ₁.gpr .r5 ∧ s.gpr .r6 = σ₁.gpr .r6 ∧ s.gpr .r7 = σ₁.gpr .r7 ∧ s.gpr .r8 = σ₁.gpr .r8 ∧
    s.gpr .r9 = σ₁.gpr .r9 ∧ s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    q8.symm, q9.symm, qsp.symm⟩, ?_⟩
  let FI := FinI (σ₁.gpr .r3) (σ₁.gpr .r4) (σ₁.gpr .r8) (σ₁.gpr .r9) σ₁.sp (σ₁.gpr .r5) (σ₁.gpr .r6)
    (σ₁.gpr .r7)
  refine CT.seq (J := FI) ?_ (fun s ⟨hs, e3, e4, e5, e6, e7, e8, e9, esp⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := finEntry_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9]⟩) hc
  · refine WP.mono (fin1_wp (fin_W hs)) fun s₁ h1 => ?_
    have hT : Covers [⟨s.gpr .r7, 16⟩] s₁.wr := by
      rw [h1.en.keeps.wr, hs.2.1]; exact covers_mem (by simp)
    refine ⟨s₁.gpr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h1.r29, e3]
    · rw [h1.r30, e4]
    · rw [h1.r31, e8]
    · rw [h1.r28, e9]
    · rw [h1.r22, e5]
    · rw [h1.r23, e6]
    · rw [h1.r20, e7]
    · rw [← esp]; exact fin_env hs h1
    · rw [← e7]; exact hT
    · rw [← e9, h1.en.keeps.wr]; exact fin_X hs
  refine CT.seq (J := FI)
    ((finTag_ct L X (o := 0) (.inl rfl)).mono fun s ⟨V, a, b, d, e, f, g, _, he, _, hx⟩ =>
      ⟨V, a, b, d, e, f, g, he, hx⟩)
    (fun s ⟨V, a, b, d, e, f, g, i, he, hT, hx⟩ => WP.mono (WP.with_rdwr (finTag_ok (L.v a b d)
      (by rw [a, b, d, e]; exact X) (o := 0) (.inl rfl)
      (a := List.replicate ((σ₁.gpr .r5).toNat % 16) 0) (ct := List.replicate (σ₁.gpr .r6).toNat 0) he
      (by rw [e]; exact hx) rfl (by simp [f]) (by simp [g]))) fun s' ⟨fo, _, wr, _⟩ =>
        ⟨V, a, b, d, e, f, g, i, fo.env, by rw [wr]; exact hT, by rw [wr]; exact hx⟩) ?_
  refine CT.seq (J := fun s => s.gpr .r31 = σ₁.gpr .r8 ∧ s.sp = σ₁.sp) ?_
    (fun s ⟨V, a, b, d, _, f, g, i, he, hT, _⟩ => WP.mono (tagOut_ok he (by rw [i]; exact hT)
      (by rw [i, d]; exact dtw)) fun s' ⟨_, _, hg, hk⟩ =>
        ⟨by rw [hg _ (by decide), he.r31, d], by rw [hk.sp, he.sp]⟩) ?_
  · obtain ⟨_, hc⟩ := tagOut_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, _, i₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, _, i₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.r31, h₂.r31, d₁, d₂]
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .r8) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.Sm4Gcm.PPC64LE
