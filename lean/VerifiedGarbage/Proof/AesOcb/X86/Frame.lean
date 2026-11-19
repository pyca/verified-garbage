module

public import VerifiedGarbage.Proof.AesOcb.Scratch
import VerifiedGarbage.Proof.AesOcb.X86.Init
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesOcb.X86.Callee
public import VerifiedGarbage.Proof.AesOcb.X86.Contract
import VerifiedGarbage.Proof.AesOcb.X86.Run
import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.AesGcm.X86.Absorb
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Spec.Ocb.Contract
public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Aes.X86.Ctr32
public import VerifiedGarbage.Proof.AesOcb.X86.Entry
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.AesOcb.X86.CTBase
public import VerifiedGarbage.Proof.AesOcb.X86.Hash
import VerifiedGarbage.Proof.AesOcb.X86.Setup
meta import VerifiedGarbage.Proof.AesOcb.X86.Entry
meta import VerifiedGarbage.Proof.Ocb.State
meta import VerifiedGarbage.Proof.AesOcb.X86.CTBase
meta import VerifiedGarbage.Proof.AesOcb.X86.Hash
meta import VerifiedGarbage.Proof.AesOcb.X86.Setup
meta import VerifiedGarbage.Proof.AesOcb.X86.Run
meta import VerifiedGarbage.Proof.AesGcm.X86.Loops
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
public import VerifiedGarbage.Proof.AesOcb.X86.Env
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.Proof.AesOcb.X86.HashFill
meta import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
meta import VerifiedGarbage.Proof.AesOcb.X86.Env
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Spec.Ocb
meta import VerifiedGarbage.Proof.AesOcb.X86.HashFill
meta import VerifiedGarbage.Proof.AesGcm.X86.Absorb
public import VerifiedGarbage.Proof.AesOcb.X86.Body
import VerifiedGarbage.Proof.AesOcb.X86.Nonce
import VerifiedGarbage.Proof.AesOcb.X86.LNtz
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesOcb.X86.Body
meta import VerifiedGarbage.Proof.AesOcb.X86.Nonce
meta import VerifiedGarbage.Proof.AesOcb.X86.LNtz
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesOcb.X86.PadTo
meta import VerifiedGarbage.Proof.AesOcb.X86.PadTo
import VerifiedGarbage.Proof.AesOcb.X86.NonceBlock
meta import VerifiedGarbage.Proof.AesOcb.X86.Callee
meta import VerifiedGarbage.Proof.AesOcb.X86.NonceBlock
meta import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ocb.Bytes
meta import VerifiedGarbage.Proof.Framework.Offset

/-! ### `AesOcb.X86.SealCT`, which only this module used -/

section

/-! ### `AesOcb.X86.Front`, which this module and modules that import it used -/

section

/-!
# AES-OCB on x86: up to the tag (`front`)

Untrusted: everything here is checked by Lean. `front` is the entry
(`entry_ok`), `L_$`, `L_0` and the checksum (`setup_ok`), `Offset_0`
(`nonce_ok`) and `HASH` (`hash_ok`), which leave `Pre` (`pre_ok`); then the
data (`bodySeal_ok`, `bodyOpen_ok`) and the tag at `W + d` (`tag_ok`)
(`sealFront_ok`, `openFront_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxInv ctxLstar pad lDollar)
open VG.Proof.Ocb (offAt)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq SavedAt length_bytesAt)

/-- What the entry writes: the saved registers and the slots. -/
abbrev entryR (p : Prm) : Region := ⟨w64 p.W + BitVec.ofNat 64 128, 88⟩

/-- A buffer apart from `W` and the stack and the data keeps its bytes across
a frame of `entryR :: mutR`. -/
theorem bytes_front {p : Prm} {P : BitVec 32} {len : Nat}
    (hw : (⟨w64 P, len⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩) (hb : (stk p).Disjoint ⟨w64 P, len⟩)
    (hd : (⟨w64 P, len⟩ : Region).Disjoint ⟨w64 p.D, p.n⟩) (hl : len ≤ 2 ^ 64) {m m' : Mem}
    (hf : Frame (entryR p :: mutR p) m m') : bytesAt m' (w64 P) len = bytesAt m (w64 P) len :=
  Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hw.sub_right (Region.sub_prefix (by decide))
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hb.symm
    · exact hd) hl

/-- What the pieces before the data leave, from the state `s` at the call. -/
structure Pre (p : Prm) (s s' : State) : Prop where
  env : Env p s'
  frame : Frame (entryR p :: mutR p) s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : SavedAt s'.mem p.W s
  ofs : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 ofsO) =
    Spec.Ocb.offset0 (ctxCiph s.mem (w64 p.K) p.R) p.tl (bytesAt s.mem (w64 p.N) p.nl)
  o0 : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 o0O) =
    Spec.Ocb.offset0 (ctxCiph s.mem (w64 p.K) p.R) p.tl (bytesAt s.mem (w64 p.N) p.nl)
  ck : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 ckO) = 0
  ld : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s.mem (w64 p.K))
  l0 : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (w64 p.K)) 0
  sum : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 sumO) =
    Spec.Ocb.hash (ctxCiph s.mem (w64 p.K) p.R) (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.A) p.al)
  ciph : ctxCiph s'.mem (w64 p.K) p.R = ctxCiph s.mem (w64 p.K) p.R
  inv : ctxInv s'.mem (w64 p.K) p.R = ctxInv s.mem (w64 p.K) p.R
  lstar : ctxLstar s'.mem (w64 p.K) = ctxLstar s.mem (w64 p.K)
  data : bytesAt s'.mem (w64 p.D) p.n = bytesAt s.mem (w64 p.D) p.n
  tag : bytesAt s'.mem (w64 p.T) p.tl = bytesAt s.mem (w64 p.T) p.tl

/-- The key context misses `entryR :: mutR`. -/
theorem k_front {p : Prm} (L : Lay p) : ∀ r ∈ entryR p :: mutR p, (⟨w64 p.K, 256⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact L.k_w' (by decide)
  · exact k_mut L r hr

theorem front_ciph {p : Prm} (L : Lay p) {m m' : Mem} (h : Frame (entryR p :: mutR p) m m') :
    ctxCiph m' (w64 p.K) p.R = ctxCiph m (w64 p.K) p.R ∧ ctxInv m' (w64 p.K) p.R = ctxInv m (w64 p.K) p.R ∧
      ctxLstar m' (w64 p.K) = ctxLstar m (w64 p.K) := by
  have hb := L.rounds_le
  refine ⟨?_, ?_, Proof.Ocb.blockAtMem_frame h fun r hr => (k_front L r hr).sub_left (Offset.sub_base _ (by decide))⟩
  · unfold ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame h (fun r hr => (k_front L r hr).sub_left (Region.sub_prefix (by omega_using [hb])))
      (by omega_using [hb])]
  · unfold ctxInv
    rw [Proof.AesGcm.X86.bytesAt_frame h (fun r hr => (k_front L r hr).sub_left (Region.sub_prefix (by omega_using [hb])))
      (by omega_using [hb])]

theorem mut_front {p : Prm} {m m' : Mem} (h : Frame (mutR p) m m') : Frame (entryR p :: mutR p) m m' :=
  h.mono fun _ hr => List.mem_cons_of_mem _ hr

theorem entry_front {p : Prm} {m m' : Mem} (h : Frame [entryR p] m m') : Frame (entryR p :: mutR p) m m' :=
  h.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..

/-- The saved registers, after a frame within `mutR`. -/
theorem saved_mut {p : Prm} (L : Lay p) {m m' : Mem} (h : Frame (mutR p) m m') {s₀ : State}
    (S : SavedAt m p.W s₀) : SavedAt m' p.W s₀ := SavedAt.mut L h S

theorem pre_ok (v : BlocksImpl) {s : State} (h : onePre s) :
    WP isa (.seq ocbEntry (.seq (.block setup) (.seq (nonce (callees v)) (hash (callees v))))) s
      (Pre (prmOf s) s) := by
  obtain L := lay_of h
  generalize hp : prmOf s = p at L
  refine WP.seq (WP.mono (hp ▸ entry_ok h) fun s₁ En => ?_)
  obtain fr₁ := entry_front En.frame
  obtain ⟨c₁, i₁, l₁⟩ := front_ciph L fr₁
  obtain hN₁ := bytes_front L.n_w L.bn L.n_d (by have := L.nl15; omega_using [this]) fr₁
  obtain hA₁ := bytes_front L.a_w L.ba L.a_d (by have := L.aw; omega_using [this]) fr₁
  obtain hD₁ := Proof.AesGcm.X86.bytesAt_frame En.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)) (by have := L.dw; omega_using [this])
  obtain hT₁ := bytes_front L.t_w L.bt L.t_d (by have := L.tl16; omega_using [this]) fr₁
  -- `L_$`, `L_0` and the checksum
  obtain ⟨s₂, run₂, P₂⟩ := setup_ok L En.env
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  obtain f₂ : Frame (mutR p) s₁.mem s₂.mem := P₂.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp
  obtain E₂ : Env p s₂ := En.env.mut L (by rw [P₂.gpr _ (by decide) (by decide) (by decide) (by decide), En.env.ebp])
    (by rw [P₂.gpr _ (by decide) (by decide) (by decide) (by decide), En.env.esp]) P₂.rd P₂.wr f₂
  -- `Offset_0`
  refine WP.seq (WP.mono (nonce_ok v L E₂) fun s₃ P₃ => ?_)
  obtain f₃ : Frame (mutR p) s₂.mem s₃.mem := wR_mut P₃.frame
  obtain f₁₃ := f₂.trans f₃
  obtain ⟨c₂, -, l₂⟩ := front_ciph L (mut_front f₂)
  obtain hN₂ := nonce_mut L f₂
  -- `HASH`
  obtain C : HCtx p (ctxCiph s₃.mem (w64 p.K) p.R) (ctxLstar s₃.mem (w64 p.K)) (bytesAt s₃.mem (w64 p.A) p.al) s₃ :=
    ⟨L, rfl, rfl, rfl⟩
  obtain hl0₃ : blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s₃.mem (w64 p.K)) 0 := by
    rw [P₃.keep (by decide) (by decide), P₂.l0, (front_ciph L (mut_front f₃)).2.2, l₂]
  refine WP.mono (hash_ok v C P₃.env hl0₃) fun s₄ ⟨E₄, F₄, sum₄, rd₄, wr₄⟩ => ?_
  obtain f₄ : Frame (mutR p) s₃.mem s₄.mem := wR_mut (hashR_wR F₄)
  obtain f₁₄ := f₁₃.trans f₄
  obtain fr := fr₁.trans (mut_front f₁₄)
  obtain ⟨c₄, i₄, l₄⟩ := front_ciph L fr
  obtain ⟨c₃, -, l₃⟩ := front_ciph L (mut_front f₁₃)
  obtain k₄ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ (64 ≤ d ∧ d + 16 ≤ 96) ∨ (176 ≤ d ∧ d + 16 ≤ 220) ∨
      (224 ≤ d ∧ d + 16 ≤ 264)) →
      blockAtMem s₄.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 d) :=
    fun {d} hd => Proof.Ocb.blockAtMem_frame F₄ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Lay.w_w (by simp only [sumO]; omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact Lay.w_w (by simp only [lO]; omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact Lay.w_w (by simp only [ohO]; omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact Lay.w_w (by simp only [kO]; omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact Lay.w_w (by simp only [hlO]; omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact Lay.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)
      · exact (L.bw' (by omega_using [hd])).symm
  obtain kS : ∀ {d : Nat}, d + 16 ≤ 128 → 32 ≤ d → d + 16 ≤ 112 →
      blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem s₂.mem (w64 p.W + BitVec.ofNat 64 d) :=
    fun _ h₁ h₂ => P₃.keep h₁ h₂
  refine ⟨E₄, fr, by rw [rd₄, P₃.rd, P₂.rd, En.rd], by rw [wr₄, P₃.wr, P₂.wr, En.wr], saved_mut L f₁₄ En.saved,
    ?_, ?_, ?_, ?_, ?_, ?_, c₄, i₄, l₄, ?_, ?_⟩
  · rw [k₄ (by decide), P₃.ofs, c₂, c₁, hN₂, hN₁, ← hp]
  · rw [k₄ (by decide), P₃.o0, c₂, c₁, hN₂, hN₁, ← hp]
  · rw [k₄ (by decide), kS (by decide) (by decide) (by decide), P₂.ck]
  · rw [k₄ (by decide), kS (by decide) (by decide) (by decide), P₂.ld, l₁]
  · rw [k₄ (by decide), kS (by decide) (by decide) (by decide), P₂.l0, l₁]
  · rw [sum₄, c₃, l₃, c₁, l₁, aad_mut L f₁₃, hA₁]
  · rw [data_wR L (hashR_wR F₄), data_wR L P₃.frame, data_wR L (P₂.frame.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp), hD₁]
  · rw [tag_mut L f₁₄, hT₁]

theorem seq_cont3 {a b c d k : Prog isa} {s : State} {P Q : State → Prop}
    (h : WP isa (.seq a (.seq b (.seq c d))) s P) (hk : ∀ t, P t → WP isa k t Q) :
    WP isa (.seq a (.seq b (.seq c (.seq d k)))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h₁ => WP.seq (WP.mono (WP.seq_iff.mp h₁) fun _ h₂ =>
    WP.seq (WP.mono (WP.seq_iff.mp h₂) fun _ h₃ => WP.seq (WP.mono h₃ hk))))

/-- `body`'s frame misses a block of `W` outside the offset, the checksum,
`[96, 128)` and `[144, 160)`. -/
theorem body_keep {p : Prm} (L : Lay p) {m m' : Mem} (h : Frame (bodyR p) m m') {d : Nat}
    (hd : d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (128 ≤ d ∧ d + 16 ≤ 144) ∨ (160 ≤ d ∧ d + 16 ≤ 216)) :
    blockAtMem m' (w64 p.W + BitVec.ofNat 64 d) = blockAtMem m (w64 p.W + BitVec.ofNat 64 d) :=
  Proof.Ocb.blockAtMem_frame h fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (by omega_using [hd]) (by omega_using [hd]) (by decide)
    · exact Lay.w_w (by omega_using [hd]) (by omega_using [hd]) (by decide)
    · exact Lay.w_w (by simp only [t2O]; omega_using [hd]) (by omega_using [hd]) (by decide)
    · exact Lay.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)
    · exact Lay.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)
    · exact (L.bw' (by omega_using [hd])).symm
    · exact (L.d_w' (by omega_using [hd])).symm

/-- What `tag d` writes, within `mutR`. -/
theorem tagR_mut {p : Prm} {d : Nat} (hd : d = tagO ∨ d = t2O) {m m' : Mem}
    (h : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 d, 16⟩,
      ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, stk p] m m') : Frame (mutR p) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact inMut_w p (.inl (by decide))
  · rcases hd with rfl | rfl
    · exact inMut_w p (.inl (by decide))
    · exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  · exact inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩)))
  · exact inMut_stk p

/-- The data across `tag`. -/
theorem data_tag {p : Prm} (L : Lay p) {d : Nat} (hd : d = tagO ∨ d = t2O) {m m' : Mem}
    (h : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 d, 16⟩,
      ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, stk p] m m') :
    bytesAt m' (w64 p.D) p.n = bytesAt m (w64 p.D) p.n :=
  Proof.AesGcm.X86.bytesAt_frame h (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.d_w' (by decide)
    · exact L.d_w' (by rcases hd with rfl | rfl <;> decide)
    · exact L.d_w' (by decide)
    · exact L.bd.symm) (by have := L.dw; omega_using [this])

/-- What `front` leaves: the environment, our caller's registers, the data
and the tag at `W + d`. -/
structure Front (p : Prm) (s s' : State) : Prop where
  env : Env p s'
  frame : Frame (entryR p :: mutR p) s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : SavedAt s'.mem p.W s

/-- `front` for `seal`: the ciphertext over the data and the tag at `W`. -/
theorem sealFront_ok (v : BlocksImpl) {s : State} (h : onePre s) :
    WP isa (front (callees v) true tagO) s fun s' => Front (prmOf s) s s' ∧
      Spec.Ocb.encryptWith (ctxCiph s.mem (w64 (prmOf s).K) (prmOf s).R) (ctxLstar s.mem (w64 (prmOf s).K))
          (prmOf s).tl (bytesAt s.mem (w64 (prmOf s).N) (prmOf s).nl) (bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al)
          (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n) =
        (bytesAt s'.mem (w64 (prmOf s).D) (prmOf s).n, bytesAt s'.mem (w64 (prmOf s).W) (prmOf s).tl) := by
  obtain L := lay_of h
  obtain Pp := pre_ok v h
  generalize prmOf s = p at L Pp ⊢
  unfold front
  refine seq_cont3 Pp fun s₃ P₃ => ?_
  refine WP.seq (WP.mono (bodySeal_ok v L P₃.env P₃.ofs P₃.o0 P₃.ck (by rw [P₃.l0, P₃.lstar])) fun s₄ B => ?_)
  obtain F₄ : Frame (mutR p) s₃.mem s₄.mem := bodyR_mut B.frame
  obtain cK₄ : ctxCiph s₄.mem (w64 p.K) p.R = ctxCiph s.mem (w64 p.K) p.R := (ctxCiph_mut L F₄).trans P₃.ciph
  obtain ld₄ : blockAtMem s₄.mem (w64 p.W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s.mem (w64 p.K)) := by
    rw [body_keep L B.frame (d := ldO) (by decide), P₃.ld]
  obtain sum₄ : blockAtMem s₄.mem (w64 p.W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s.mem (w64 p.K) p.R) (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.A) p.al) := by
    rw [body_keep L B.frame (d := sumO) (by decide), P₃.sum]
  refine WP.mono (tag_ok v L B.env (d := tagO) (.inl rfl)) fun s₅ T₅ => ?_
  obtain F₅ : Frame (mutR p) s₄.mem s₅.mem := tagR_mut (.inl rfl) T₅.frame
  refine ⟨⟨T₅.env, P₃.frame.trans (mut_front (F₄.trans F₅)), by rw [T₅.rd, B.rd, P₃.rd],
    by rw [T₅.wr, B.wr, P₃.wr], saved_mut L (F₄.trans F₅) P₃.saved⟩, ?_⟩
  have hout := B.out
  rw [P₃.ciph, P₃.lstar, P₃.data] at hout
  have hofs := B.ofs
  rw [P₃.lstar] at hofs
  have hck := B.ck
  rw [P₃.data] at hck
  have tv := T₅.val
  rw [show w64 p.W + BitVec.ofNat 64 tagO = w64 p.W from BitVec.add_zero _] at tv
  rw [Proof.Ocb.encryptWith_eq, data_tag L (.inl rfl) T₅.frame, hout, Proof.Ocb.bytesAt_take_block _ _ L.tl16, tv,
    hck, hofs, ld₄, sum₄, cK₄]
  simp only [length_bytesAt, List.length_drop]
  by_cases hr : 0 < p.n % 16
  · have h' : p.n - 16 * (p.n / 16) > 0 := by omega_using [hr]
    simp only [h', hr, ↓reduceIte]
  · have h' : ¬ (p.n - 16 * (p.n / 16) > 0) := by omega_using [hr]
    simp only [h', hr, ↓reduceIte]

/-- `front` for `open`: the plaintext over the data and the tag at
`W + t2O`, which decide `OCB-DECRYPT` with the tag `tag`. -/
theorem openFront_ok (v : BlocksImpl) {s : State} (h : onePre s) (tag : List Byte) :
    WP isa (front (callees v) false t2O) s fun s' => Front (prmOf s) s s' ∧
      Spec.Ocb.decryptWith (ctxCiph s.mem (w64 (prmOf s).K) (prmOf s).R) (ctxInv s.mem (w64 (prmOf s).K) (prmOf s).R)
          (ctxLstar s.mem (w64 (prmOf s).K)) (prmOf s).tl (bytesAt s.mem (w64 (prmOf s).N) (prmOf s).nl)
          (bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al) (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n) tag =
        if bytesAt s'.mem (w64 (prmOf s).W + BitVec.ofNat 64 t2O) (prmOf s).tl = tag then
          some (bytesAt s'.mem (w64 (prmOf s).D) (prmOf s).n)
        else none := by
  obtain L := lay_of h
  obtain Pp := pre_ok v h
  generalize prmOf s = p at L Pp ⊢
  unfold front
  refine seq_cont3 Pp fun s₃ P₃ => ?_
  refine WP.seq (WP.mono (bodyOpen_ok v L P₃.env P₃.ofs P₃.o0 P₃.ck (by rw [P₃.l0, P₃.lstar])) fun s₄ B => ?_)
  obtain F₄ : Frame (mutR p) s₃.mem s₄.mem := bodyR_mut B.frame
  obtain cK₄ : ctxCiph s₄.mem (w64 p.K) p.R = ctxCiph s.mem (w64 p.K) p.R := (ctxCiph_mut L F₄).trans P₃.ciph
  obtain ld₄ : blockAtMem s₄.mem (w64 p.W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s.mem (w64 p.K)) := by
    rw [body_keep L B.frame (d := ldO) (by decide), P₃.ld]
  obtain sum₄ : blockAtMem s₄.mem (w64 p.W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s.mem (w64 p.K) p.R) (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.A) p.al) := by
    rw [body_keep L B.frame (d := sumO) (by decide), P₃.sum]
  refine WP.mono (tag_ok v L B.env (d := t2O) (.inr rfl)) fun s₅ T₅ => ?_
  obtain F₅ : Frame (mutR p) s₄.mem s₅.mem := tagR_mut (.inr rfl) T₅.frame
  refine ⟨⟨T₅.env, P₃.frame.trans (mut_front (F₄.trans F₅)), by rw [T₅.rd, B.rd, P₃.rd],
    by rw [T₅.wr, B.wr, P₃.wr], saved_mut L (F₄.trans F₅) P₃.saved⟩, ?_⟩
  have hout := B.out
  rw [P₃.ciph, P₃.inv, P₃.lstar, P₃.data] at hout
  have hofs := B.ofs
  rw [P₃.lstar] at hofs
  have hck := B.ck
  rw [P₃.ciph, P₃.inv, P₃.lstar, P₃.data] at hck
  rw [Proof.Ocb.decryptWith_eq, data_tag L (.inr rfl) T₅.frame, hout, Proof.Ocb.bytesAt_take_block _ _ L.tl16,
    T₅.val, hck, hofs, ld₄, sum₄, cK₄]
  simp only [length_bytesAt, List.length_drop]
  by_cases hr : 0 < p.n % 16
  · have h' : p.n - 16 * (p.n / 16) > 0 := by omega_using [hr]
    simp only [h', hr, ↓reduceIte]
  · have h' : ¬ (p.n - 16 * (p.n / 16) > 0) := by omega_using [hr]
    simp only [h', hr, ↓reduceIte]

end VG.Proof.AesOcb.X86

end

end

/-! ### `AesOcb.X86.FrontCT`, which only this module used -/

section

/-!
# AES-OCB on x86: the entry, the setup and `Offset_0` in constant time

Untrusted: everything here is checked by Lean. The entry addresses only the
stack and `W` (`entry_ct`); `setup` doubles `L_*` from the key context,
whose address it loads from its slot (`setup_ct`); `nonceBlock` copies the
nonce to an address computed from its length, loaded from its slot
(`nonceBlock_ct`); then a call and `Offset_0`, which addresses only `W`
(`nonce_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop zero4)
open VG.Proof.AesGcm.X86 (CT w64 slotv slotv_eq copyLoop_ct arg0_ok argIn_of LoopPre)

/-- The entry. -/
theorem entry_ct (p : Prm) : CT (fun s => onePre s ∧ prmOf s = p) ocbEntry := by
  rw [ocbEntry_eq]
  refine CT.seq (J := fun s => s.gpr .eax = p.W ∧ s.gpr .esp = p.SP)
    (CT.taint [.esp] (pin1 (x := p.SP) fun s h => by rw [← h.2]; rfl) (by taint_decide)) (fun s hs => ?_)
    (CT.taint [.eax, .esp] (pin2 fun _ h => h) (by taint_decide))
  have Ao := argsOk_of hs.1
  refine WP.mono (arg0_ok (argIn_of Ao.rA Ao.fa (i := 10) (by decide))) fun s' ⟨ax, sp⟩ => ⟨?_, ?_⟩
  · rw [ax, ← hs.2]; rfl
  · rw [sp, ← hs.2]; rfl

/-- `L_$`, `L_0` and the checksum. -/
theorem setup_ct {I : State → Prop} {p : Prm} (L : Lay p) (hI : ∀ s, I s → Env p s) : CT I (.block setup) := by
  show CT I (.block (([.mov .ebx (slot ctxO)] : List Instr) ++ (dbl .ebx 240 ldO ++ dbl .ebp ldO l0O ++ zero4 ckO)))
  refine RelCT.block_append
    (CT.seq (J := fun s => s.gpr .ebp = p.W ∧ s.gpr .ebx = p.K)
      (CT.taint [.ebp] (pin_ebp fun s h => (hI s h).ebp) (by taint_decide)) (fun s hs => ?_)
      (CT.taint [.ebp, .ebx] (pin2 fun _ h => h) (by taint_decide)))
  have E := hI s hs
  have hc := E.slots.ctx
  simp only [slotv_eq] at hc
  exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hc], by gregs [E.ebp], by gregs [hc]⟩

/-- The nonce block. -/
theorem nonceBlock_ct {I : State → Prop} {p : Prm} (L : Lay p) (hI : ∀ s, I s → Env p s) : CT I nonceBlock := by
  unfold nonceBlock
  refine CT.seq (J := fun s => Env p s ∧ LoopPre s p.N (p.W + BitVec.ofNat 32 (128 - p.nl)) p.nl)
    (CT.taint [.ebp] (pin_ebp fun s h => (hI s h).ebp) (by taint_decide)) (fun s hs => ?_) ?_
  · obtain ⟨s₂, run₂, E₂, lp, -⟩ := nonceHead_ok L (hI s hs)
    exact WP.of_runBlock ⟨s₂, run₂, E₂, lp⟩
  refine CT.seq (J := Env p) (copyLoop_ct (pin3 fun _ h => ⟨h.2.edi, h.2.edx, h.2.ecx⟩))
    (fun s h => WP.mono (copyW_ok L h.1 (d := 128 - p.nl) (n := p.nl) (by have := L.nl15; omega_using [this]) h.2) fun _ h' => h'.1) ?_
  rw [← List.singleton_append (x := Instr.mov .ecx (slot nlO))]
  refine RelCT.block_append
    (CT.seq (J := fun s => s.gpr .ebp = p.W ∧ s.gpr .ecx = BitVec.ofNat 32 p.nl)
      (CT.taint [.ebp] (pin_ebp fun s h => h.ebp) (by taint_decide)) (fun s (E : Env p s) => ?_)
      (CT.taint [.ebp, .ecx] (pin2 fun _ h => h) (by taint_decide)))
  have hnl := E.slots.nlen
  simp only [slotv_eq] at hnl
  exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hnl], by gregs [E.ebp], by gregs [hnl]⟩

/-- `Offset_0`. -/
theorem nonce_ct (v : BlocksImpl) {I : State → Prop} {p : Prm} (L : Lay p) (hI : ∀ s, I s → Env p s) :
    CT I (nonce (callees v)) := by
  unfold nonce
  refine CT.seq (J := Env p) (nonceBlock_ct L hI) (fun s hs => ?_) ?_
  · have E := hI s hs
    refine WP.mono (nonceBlock_ok L E) fun s₁ P₁ => ?_
    have F₁ : Frame (wR p) s.mem s₁.mem := frame_wR P₁.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact inW_wR p (.inl (by decide))
      · exact inW_wR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
    exact E.mut L (by rw [P₁.gpr _ (by decide) (by decide) (by decide) (by decide), E.ebp])
      (by rw [P₁.gpr _ (by decide) (by decide) (by decide) (by decide), E.esp]) P₁.rd P₁.wr (wR_mut F₁)
  refine CT.seq (J := Env p) (oneCall_ct v.encOk v.encCt v.encNosp v.encStack L (.inl rfl) fun _ h => h)
    (fun s E => WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L E
      (oneBlock_ok E tmpO) (DReg.w L E (d := tmpO) (n := 1) (by decide) (.inl (by decide)))) fun _ P => P.env)
    (CT.taint [.ebp] (pin_ebp fun s h => h.ebp) (by taint_decide))

end VG.Proof.AesOcb.X86

end

end

/-! ### `AesOcb.X86.HashCT`, which only this module used -/

section

/-!
# AES-OCB on x86: `HASH` in constant time

Untrusted: everything here is checked by Lean. `HASH` runs a loop of
chunks, each a loop filling the buffer (`hashFill_ct`, `fillLoop_ct`), a
call and a loop adding the buffer to the sum (`hashSum_ct`): `chunk_ct`;
the number of chunks and of their blocks is public (`hashLoop_ct`). The
counts and the buffer's address are loaded from their slots. Then the rest
(`hashRest_ct`) if there is one (`hashTail_ct`): `hash_ct`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop zero4)
open VG.Proof.AesGcm.X86 (CT w64 w64_add slotv slotv_eq toNat_add32 covers_off)

/-- The fill loop's state after `i` of the `c` blocks of a chunk from block
`j`, for some cipher, `L_*`, associated data and start. -/
def FillI (p : Prm) (j c i : Nat) (t : State) : Prop :=
  ∃ ciph l a s₀, HCtx p ciph l a s₀ ∧ FillInv p ciph l a s₀ j c t i

/-- `HASH`'s state after `j` whole blocks. -/
def HI (p : Prm) (j : Nat) (t : State) : Prop :=
  ∃ ciph l a s₀, HCtx p ciph l a s₀ ∧ HInv p ciph l a s₀ t j

/-- One block into the buffer. -/
theorem hashFill_ct {p : Prm} (L : Lay p) {j c i : Nat} (hi : i < c) (hjc : j + c ≤ p.al / 16) :
    CT (FillI p j c i) hashFill := by
  have hal := L.al32
  unfold hashFill
  refine CT.seq (J := fun t => Env p t ∧ t.gpr .esi = p.A + BitVec.ofNat 32 (16 * (j + i)) ∧
      slotv t.mem p.W fpO = p.W + BitVec.ofNat 32 (bufO + 16 * i))
    (lNtz_ct L (i := j + i + 1) (by omega_using []) (by omega_using [hi, hjc, hal]) fun t ⟨_, _, _, _, _, F⟩ => ⟨F.env, F.edi⟩)
    (fun t ⟨_, _, _, _, _, F⟩ => WP.mono (lNtz_ok L F.env (by omega_using []) (by omega_using [hi, hjc, hal]) F.edi F.l0) fun t₁ P₁ =>
      ⟨P₁.env L F.env, by rw [P₁.gpr _ (by decide) (by decide) (by decide), F.esi], by
        rw [← F.fp]
        exact P₁.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 fpO, 4⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)) (by decide)⟩) ?_
  simp only [List.append_assoc, List.singleton_append]
  refine RelCT.block_append (CT.seq (J := fun t => Env p t ∧ t.gpr .esi = p.A + BitVec.ofNat 32 (16 * (j + i)) ∧
      slotv t.mem p.W fpO = p.W + BitVec.ofNat 32 (bufO + 16 * i))
    (CT.taint [.ebp] (pin_ebp fun t h => h.1.ebp) (by taint_decide)) (fun t h => ?_) ?_)
  · obtain ⟨E, si, fp⟩ := h
    obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := xor16W_ok L E (s := lO) (d := ohO) (by decide) (by decide)
      (.inl (by decide))
    have f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩] t.mem t₂.mem := by
      rw [m₂]; exact xorMem16_frame _ _ _ _ _
    refine WP.of_runBlock ⟨t₂, run₂, E.mut L (by rw [g₂ _ (by decide), E.ebp]) (by rw [g₂ _ (by decide), E.esp])
      rd₂ wr₂ (frame_toMut f₂ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))),
      by rw [g₂ _ (by decide), si], ?_⟩
    rw [← fp]
    exact f₂.readW (r := ⟨w64 p.W + BitVec.ofNat 64 fpO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (by decide) (by decide) (by decide)) (by decide)
  refine load_blk_ct L (r := .edx) (o := fpO) (by decide) (fun t h => ⟨h.1, h.2.2⟩)
    (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)) (CT.taint [.ebp, .esi, .edx]
      (pin3 fun t h => ⟨Ld.reg (by decide) (fun s h => h.1.ebp) t h, Ld.reg (by decide) (fun s h => h.2.1) t h,
        by obtain ⟨_, _, hv, _⟩ := h; exact hv⟩) (by taint_decide))

/-- The fill loop: `c` blocks into the buffer. -/
theorem fillLoop_ct {p : Prm} (L : Lay p) {j c : Nat} (hc0 : 0 < c) (hc : c ≤ 8) (hjc : j + c ≤ p.al / 16) :
    CT (FillI p j c 0) (.loop hashFill .ne) := by
  refine (CT.loopN (fun n t => 0 < n ∧ n ≤ c ∧ FillI p j c (c - n) t) (fun n => ?_)
    (fun n t ⟨hn0, hn, _, _, _, _, C, F⟩ => WP.mono (fill_step C hc hjc (by omega_using [hc0, hn0]) F) fun t' ⟨F', zf'⟩ =>
      ⟨hn0, by rw [eval_ne zf']; congr 1; by_cases h : n = 1 <;> simp [h] <;> omega_arith,
        fun h1 => ⟨by omega_using [hn0, h1], by omega_using [hn], _, _, _, _, C, by rw [show c - (n - 1) = c - n + 1 by omega_using [hn0, hn]]; exact F'⟩⟩) c).mono
    fun t h => ⟨hc0, Nat.le_refl _, by rw [Nat.sub_self]; exact h⟩
  by_cases hn : 0 < n
  · exact (hashFill_ct L (i := c - n) (by omega_using [hc0, hn]) hjc).mono fun _ h => h.2.2
  · exact RelCT.of_false fun _ _ h => hn h.1.1

/-- The sum of the buffer. -/
theorem hashSum_ct {p : Prm} (L : Lay p) {c : Nat} :
    CT (fun t => Env p t ∧ slotv t.mem p.W cntO = BitVec.ofNat 32 c) hashSum := by
  unfold hashSum
  exact load_ct L (r := .ebx) (o := cntO) (by decide) (fun t h => h)
    (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))
    (CT.taint [.ebp, .ebx] (pin2 fun t h => ⟨Ld.reg (by decide) (fun s h => h.1.ebp) t h,
      by obtain ⟨_, _, hv, _⟩ := h; exact hv⟩) (by taint_decide))

/-- A chunk, from block `j`. -/
theorem chunk_ct (v : BlocksImpl) {p : Prm} (L : Lay p) {j : Nat} (hj : j < p.al / 16) :
    CT (HI p j) (hashChunk (callees v)) := by
  have hal := L.al32
  unfold hashChunk
  refine RelCT.assoc (CT.seq (J := fun t => HI p j t ∧ t.gpr .ebx = BitVec.ofNat 32 (min 8 (p.al / 16 - j)))
    (load_ct L (r := .ebx) (o := hlO) (v := BitVec.ofNat 32 (p.al / 16 - j)) (by decide)
      (fun t ⟨_, _, _, _, _, H⟩ => ⟨H.env, H.hl⟩) (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))
      (CT.taint [.ebx] (pin1 fun t h => by obtain ⟨_, _, hv, _⟩ := h; exact hv) (by taint_decide)))
    (fun t ⟨_, _, _, _, C, H⟩ => WP.mono (chunkHead_ok C H) fun t' ⟨H', bx⟩ => ⟨⟨_, _, _, _, C, H'⟩, bx⟩) ?_)
  generalize hc : min 8 (p.al / 16 - j) = c
  have hc0 : 0 < c := by omega_using [hj, hc]
  have hc8 : c ≤ 8 := by omega_using [hc]
  have hjc : j + c ≤ p.al / 16 := by omega_using [hj, hc]
  -- The chunk's count and the buffer's start.
  refine CT.seq (J := FillI p j c 0)
    (CT.taint [.ebp] (pin_ebp fun t h => by obtain ⟨⟨_, _, _, _, _, H⟩, _⟩ := h; exact H.env.ebp) (by taint_decide))
    (fun t ⟨⟨_, _, _, _, C, H⟩, bx⟩ => by
      obtain ⟨t₁, run₁, F⟩ := chunkStart_ok C H bx
      exact WP.of_runBlock ⟨t₁, run₁, _, _, _, _, C, F⟩) ?_
  -- The fill loop.
  refine CT.seq (J := FillI p j c c) (fillLoop_ct L hc0 hc8 hjc)
    (fun t ⟨_, _, _, _, C, F⟩ => WP.mono (fill_ok C hc0 hc8 hjc F) fun t' F' => ⟨_, _, _, _, C, F'⟩) ?_
  -- The call.
  have hargs : ∀ t, FillI p j c c t → ∃ s₁, runBlock isa [.mov .edx (.reg .ebp), .alu .add .edx (imm bufO),
      .mov .ebx (slot cntO)] t = some s₁ ∧ s₁.gpr .edx = p.W + BitVec.ofNat 32 bufO ∧
      s₁.gpr .ebx = BitVec.ofNat 32 c ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s₁.gpr r = t.gpr r) ∧ s₁.mem = t.mem ∧
      s₁.rd = t.rd ∧ s₁.wr = t.wr := fun t ⟨_, _, _, _, _, F⟩ => by
    have hcnt := F.cnt
    simp only [slotv_eq] at hcnt
    exact ⟨_, by grun [F.env.ebp, L.aW, F.env.perm.wR, hcnt], by gregs [F.env.ebp], by gregs [hcnt],
      fun r _ h₂ _ h₄ => by gregs [h₂, h₄], by gmems [], by gmems [], by gmems []⟩
  have hD : ∀ t, FillI p j c c t → DReg p t (p.W + BitVec.ofNat 32 bufO) c := fun t ⟨_, _, _, _, _, F⟩ =>
    DReg.w L F.env (d := bufO) (n := c) (by simp only [bufO, scrO]; omega_using [hc]) (.inr (.inr (.inr (by decide))))
  refine CT.seq (J := fun t => Env p t ∧ slotv t.mem p.W cntO = BitVec.ofNat 32 c)
    (callBlocks_ct v.encOk v.encCt v.encNosp v.encStack L
      (fun t h => ⟨by obtain ⟨_, _, _, _, _, F⟩ := h; exact F.env, hD t h, hargs t h⟩)
      fun hJ => by exact CT.taint [.ebp] (pin_ebp hJ) (by taint_decide))
    (fun t h => ?_) ?_
  · obtain ⟨_, _, _, _, _, F⟩ := h
    refine WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L F.env
      (hargs t ⟨_, _, _, _, ‹_›, F⟩) (hD t ⟨_, _, _, _, ‹_›, F⟩)) fun t' P => ⟨P.env, ?_⟩
    rw [← F.cnt]
    have aB : w64 (p.W + BitVec.ofNat 32 bufO) = w64 p.W + BitVec.ofNat 64 bufO := L.aW (by decide)
    exact P.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 cntO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [aB]; exact Lay.w_w (.inl (by decide)) (by decide) (by simp only [bufO]; omega_using [hc])
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)
  -- The sum, and the blocks left.
  refine CT.seq (J := Env p) (hashSum_ct L) (fun t ⟨E, hcnt⟩ => WP.mono (hashSum_ok L E hc0 hc8 hcnt
      (g := fun k => blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 (bufO + 16 * k))) fun _ _ => rfl)
      fun t' ⟨fr, _, g, rd, wr⟩ => E.mut L (by rw [g _ (by decide) (by decide) (by decide), E.ebp])
        (by rw [g _ (by decide) (by decide) (by decide), E.esp]) rd wr
        (frame_toMut fr fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide))))
    (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide))

/-- The chunks: from block `8 (k − n)`, `n` of the `k = ⌈m / 8⌉` left. -/
theorem hashLoop_ct (v : BlocksImpl) {p : Prm} (L : Lay p) (hm : 0 < p.al / 16) :
    CT (HI p 0) (.loop (hashChunk (callees v)) .ne) := by
  have hal := L.al32
  have hk : ∀ n, 0 < n → n ≤ (p.al / 16 + 7) / 8 → 8 * ((p.al / 16 + 7) / 8 - n) < p.al / 16 := fun n h₁ h₂ => by
    omega_using [hm, h₁]
  refine (CT.loopN (fun n t => 0 < n ∧ n ≤ (p.al / 16 + 7) / 8 ∧ HI p (8 * ((p.al / 16 + 7) / 8 - n)) t)
    (fun n => ?_) (fun n t ⟨hn0, hn, _, _, _, _, C, H⟩ => ?_) ((p.al / 16 + 7) / 8)).mono
    fun t h => ⟨by omega_using [hm], Nat.le_refl _, by rw [Nat.sub_self]; exact h⟩
  · by_cases h : 0 < n ∧ n ≤ (p.al / 16 + 7) / 8
    · exact (chunk_ct v L (hk n h.1 h.2)).mono fun _ h => h.2.2
    · exact RelCT.of_false fun _ _ h' => h ⟨h'.1.1, h'.1.2.1⟩
  refine WP.mono (hashChunk_ok v C H (hk n hn0 hn)) fun t' ⟨H', zf'⟩ => ⟨hn0, ?_, fun h1 => ⟨by omega_using [hn0, h1], by omega_using [hn],
    _, _, _, _, C, ?_⟩⟩
  · rw [eval_ne zf']; congr 1; by_cases h : n = 1 <;> simp [h] <;> omega_arith
  · rw [show 8 * ((p.al / 16 + 7) / 8 - (n - 1)) = 8 * ((p.al / 16 + 7) / 8 - n) +
      min 8 (p.al / 16 - 8 * ((p.al / 16 + 7) / 8 - n)) by omega_using [hn, h1]]
    exact H'

/-- The rest of the associated data. -/
theorem hashRest_ct (v : BlocksImpl) {p : Prm} (L : Lay p) (hr : 0 < p.al % 16) :
    CT (HI p (p.al / 16)) (hashRest (callees v)) := by
  have hal := L.aw
  have hS : ∀ t, Env p t → SBuf p t (p.A + BitVec.ofNat 32 (16 * (p.al / 16))) (p.al % 16) := fun t E => by
    have a16 : w64 (p.A + BitVec.ofNat 32 (16 * (p.al / 16))) = w64 p.A + BitVec.ofNat 64 (16 * (p.al / 16)) :=
      w64_add (by omega_using [hr, hal])
    have sub : Region.Sub ⟨w64 (p.A + BitVec.ofNat 32 (16 * (p.al / 16))), p.al % 16⟩ ⟨w64 p.A, p.al⟩ := by
      rw [a16]; exact Offset.sub_base _ (by omega_using [])
    refine ⟨?_, L.a_w.sub_left sub, ?_⟩
    · rw [toNat_add32 (by omega_using [hr, hal])]; omega_using [hal]
    · rw [a16]; exact covers_off E.perm.aad (by omega_using []) (by omega_using [hal])
  -- After the head: the environment, the rest's address and length.
  let J : State → Prop := fun t => Env p t ∧ t.gpr .esi = p.A + BitVec.ofNat 32 (16 * (p.al / 16)) ∧
    slotv t.mem p.W restO = BitVec.ofNat 32 (p.al % 16)
  unfold hashRest
  refine CT.seq (J := J) ?_ (fun t ⟨_, _, _, _, _, H⟩ => ?_) ?_
  · exact load_blk_ct L (r := .ebx) (o := ctxO) (by decide) (fun t ⟨_, _, _, _, _, H⟩ => ⟨H.env, H.env.slots.ctx⟩)
      (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))
      (CT.taint [.ebp, .ebx] (pin2 fun t h => ⟨Ld.reg (by decide)
        (fun s (h : HI p (p.al / 16) s) => by obtain ⟨_, _, _, _, _, H⟩ := h; exact H.env.ebp) t h,
        by obtain ⟨_, _, hv, _⟩ := h; exact hv⟩) (by taint_decide))
  · obtain ⟨t₂, run₂, E₂, m₂, g₂, rd₂, wr₂⟩ := hashRestHead_ok L H.env
    refine WP.of_runBlock ⟨t₂, run₂, E₂, by rw [g₂ _ (by decide) (by decide), H.esi], ?_⟩
    rw [← H.rest, slotv_eq, slotv_eq, m₂]
    exact (xorMem16_frame _ _ _ _ _).readW (r := ⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide)
  -- `pad(A_*)`, its offset, the call and the sum.
  refine CT.seq (J := Env p) (padTo_ct L (.inl rfl) fun t h => h)
    (fun t ⟨E, si, rest⟩ => WP.mono (padTo_ok L E (d := bufO) (cO := restO) hr (by omega_using []) (by decide) (by decide)
      (.inl (by decide)) si rest (hS t E)) fun t' ⟨fr, _, g, rd, wr⟩ =>
        E.mut L (by rw [g _ (by decide) (by decide) (by decide) (by decide), E.ebp])
          (by rw [g _ (by decide) (by decide) (by decide) (by decide), E.esp]) rd wr
          (frame_toMut fr fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩)))))
    ?_
  refine CT.seq (J := Env p) (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun t E => ?_) ?_
  · obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := xor16W_ok L E (s := ohO) (d := bufO) (by decide) (by decide)
      (.inl (by decide))
    exact WP.of_runBlock ⟨t₂, run₂, E.mut L (by rw [g₂ _ (by decide), E.ebp]) (by rw [g₂ _ (by decide), E.esp])
      rd₂ wr₂ (frame_toMut (by rw [m₂]; exact xorMem16_frame _ _ _ _ _) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩))))⟩
  refine CT.seq (J := Env p) (oneCall_ct v.encOk v.encCt v.encNosp v.encStack L (.inr rfl) fun _ h => h)
    (fun t E => WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L E
      (oneBlock_ok E bufO) (DReg.w L E (d := bufO) (n := 1) (by decide) (.inr (.inr (.inr (by decide))))))
      fun _ P => P.env)
    (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide))

/-- The rest, if there is one. -/
theorem hashTail_ct (v : BlocksImpl) {p : Prm} (L : Lay p) :
    CT (HI p (p.al / 16)) (.seq (.block [.mov .eax (slot restO), .alu .test .eax (.reg .eax)])
      (.ite .e (.block []) (hashRest (callees v)))) := by
  refine load_ct L (r := .eax) (o := restO) (v := BitVec.ofNat 32 (p.al % 16)) (by decide)
    (fun t ⟨_, _, _, _, _, H⟩ => ⟨H.env, H.rest⟩) (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)) ?_
  refine CT.seq (J := fun t => HI p (p.al / 16) t ∧ t.zf = some (decide (p.al % 16 = 0)))
    (CT.taint [] (fun _ _ _ _ _ h => by simp at h) (by taint_decide)) (fun t ⟨s₀, h₀, ax, g, m, rd, wr⟩ => ?_)
    (CT.ite (decide (p.al % 16 = 0)) (fun _ h => eval_e h.2) (fun _ => CT.nil)
      (fun hb => (hashRest_ct v L (by have := of_decide_eq_false hb; omega_using [this])).mono fun _ h => h.1))
  obtain ⟨_, _, _, _, C, H⟩ := h₀
  have hal := L.al32
  refine WP.of_runBlock ⟨_, by grun [], ⟨_, _, _, _, C, H.of_keep (fun r h₁ _ _ _ => by gregs [g r h₁]) (by gmems [m])
    (by gmems [rd]) (by gmems [wr])⟩, ?_⟩
  gmems [ax, BitVec.and_self, beq_zero32 (show p.al % 16 < 2 ^ 32 by omega_using [])]

/-- `HASH`. -/
theorem hash_ct (v : BlocksImpl) {p : Prm} (L : Lay p) :
    CT (fun t => ∃ ciph l a, HCtx p ciph l a t ∧ Env p t ∧
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt l 0) (Impl.AesOcb.X86.hash (callees v)) := by
  unfold Impl.AesOcb.X86.hash
  refine CT.seq (J := fun t => HI p 0 t ∧ t.zf = some (decide (p.al / 16 = 0)))
    (CT.taint [.ebp] (pin_ebp fun _ h => by obtain ⟨_, _, _, _, E, _⟩ := h; exact E.ebp) (by taint_decide))
    (fun t ⟨_, _, _, C, E, hl0⟩ => WP.mono (hashHead_ok C E hl0) fun t' ⟨H, zf⟩ => ⟨⟨_, _, _, _, C, H⟩, zf⟩) ?_
  refine CT.seq (J := HI p (p.al / 16))
    (CT.ite (decide (p.al / 16 = 0)) (fun _ h => eval_e h.2) (fun _ => CT.nil)
      (fun hb => (hashLoop_ct v L (by have := of_decide_eq_false hb; omega_using [this])).mono fun _ h => h.1))
    (fun t ⟨⟨_, _, _, _, C, H⟩, zf⟩ => WP.ite (decide (p.al / 16 = 0)) (eval_e zf)
      (fun hb => WP.block_nil ⟨_, _, _, _, C, by rw [of_decide_eq_true hb]; exact H⟩)
      (fun hb => WP.mono (hashLoop_ok v C H (by have := of_decide_eq_false hb; omega_using [this])) fun t' H' =>
        ⟨_, _, _, _, C, H'⟩)) (hashTail_ct v L)

end VG.Proof.AesOcb.X86

end

end

/-! ### `AesOcb.X86.BodyCT`, which only this module used -/

section

/-!
# AES-OCB on x86: the data and the tag in constant time

Untrusted: everything here is checked by Lean. A pass over the whole blocks
runs for their number, public, four at a time and then one at a time, each
block's `L_{ntz(i)}` in the table or where `lAddr` finds it from the block's
index (`lAddr_ct`, `quad_ct`, `single_ct`, `pass_ct`);
`whole` is the table, as long as the public number of blocks needs
(`ltable_ct`), then two passes around a call (`wholeIn_ct`, `whole_ct`);
the rest addresses the
data's end and `W` (`rest_ct`); `body` branches on the data's length
(`body_ct`); the tag addresses only `W` (`tag_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxInv ctxLstar)
open VG.Proof.Ocb (offAt ckOf)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop xorLoop)
open VG.Proof.AesGcm.X86 (CT w64 w64_add slotv slotv_eq xorLoop_ct runBlock_app_of length_bytesAt)

/-! ## A pass -/

/-- Checksums by `fC` from `c0`. -/
def ckRec (fC : Block → Block → Block → Block) (O0 l : Block) (X : Nat → Block) (c0 : Block) : Nat → Block
  | 0 => c0
  | k + 1 => fC (ckRec fC O0 l X c0 k) (X k) (offAt O0 l (k + 1))

/-- A pass's state after `i` of its `m` blocks, for some offset, `L_*`,
blocks and checksums. -/
def PassI (p : Prm) (fC : Block → Block → Block → Block) (m i : Nat) (t : State) : Prop :=
  ∃ O0 l X ckF t₀, (∀ k < m, ckF (k + 1) = fC (ckF k) (X k) (offAt O0 l (k + 1))) ∧
    PassInv p m O0 l X (fun b o => b ^^^ o) ckF t₀ t i

theorem PassI.start {p : Prm} {fC : Block → Block → Block → Block} {m : Nat} {t : State} (E : Env p t)
    (hsi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * 0)) (hdi : t.gpr .edi = BitVec.ofNat 32 (0 + 1))
    (hbx : t.gpr .ebx = BitVec.ofNat 32 (m - 0)) {l : Block}
    (hl0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0) (hT : Tbl p l m t.mem) :
    PassI p fC m 0 t :=
  ⟨_, l, fun k => blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * k)),
    ckRec fC (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO)) l
      (fun k => blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * k))) (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO)),
    t, fun _ _ => rfl,
    { env := E, frame := Frame.refl _ _, rd := rfl, wr := rfl, esi := hsi, edi := hdi, ebx := hbx, ofs := rfl,
      ck := rfl, blk := fun k _ => by simp, l0 := hl0, tbl := hT, gpr := fun _ _ _ _ _ _ _ => rfl }⟩

/-- A pass's state among its blocks, after `i` of its `m`, with `b` in
`ebx`. -/
def XI (p : Prm) (fC : Block → Block → Block → Block) (m i b : Nat) (t : State) : Prop :=
  ∃ O0 l X ckF t₀, (∀ k < m, ckF (k + 1) = fC (ckF k) (X k) (offAt O0 l (k + 1))) ∧
    XInv p m O0 l X (fun b o => b ^^^ o) ckF t₀ t i ∧ t.gpr .ebx = BitVec.ofNat 32 b

/-- `lAddr`, for the public `i` in `edi`: it branches on `i`, and addresses
`W` and the table. -/
theorem lAddr_ct {I : State → Prop} {p : Prm} (L : Lay p) {i : Nat} (hi : 0 < i) (hi' : i < 2 ^ 32)
    (hI : ∀ s, I s → Env p s ∧ s.gpr .edi = BitVec.ofNat 32 i ∧
      ∃ l, blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0) : CT I lAddr := by
  unfold lAddr
  refine CT.seq (J := fun t => Env p t ∧ t.gpr .edi = BitVec.ofNat 32 i ∧ t.gpr .eax = BitVec.ofNat 32 i ∧
      t.zf = some (decide (i % 64 = 0)) ∧ ∃ l, blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0)
    (CT.taint [.ebp, .edi] (pin2 fun s h => ⟨(hI s h).1.ebp, (hI s h).2.1⟩) (by taint_decide)) (fun s hs => ?_) ?_
  · obtain ⟨E, hdi, l, hl0⟩ := hI s hs
    obtain ⟨s₁, run₁, ax₁, zf₁, g₁, m₁, -, rd₁, wr₁⟩ := lAddrHead_ok hi' hdi
    exact WP.of_runBlock ⟨s₁, run₁, E.keep (g₁ _ (by decide)) (g₁ _ (by decide)) rd₁ wr₁ m₁,
      by rw [g₁ _ (by decide), hdi], ax₁, zf₁, l, by rw [m₁, hl0]⟩
  refine CT.ite (decide (i % 64 = 0)) (fun _ h => eval_e h.2.2.2.1) (fun _ => ?_) (fun _ => ?_)
  · -- a multiple of 64: `lNtz`
    refine CT.seq (J := fun t => Env p t ∧ t.gpr .edi = BitVec.ofNat 32 i ∧
        ∃ l, blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0)
      (CT.taintS [.ebp] (pin_ebp fun _ h => h.1.ebp) (by taint_decide)) (fun t ⟨E, hdi, _, _, l, hl0⟩ => ?_)
      (CT.seq (J := fun t => t.gpr .ebp = p.W) (lNtz_ct L hi hi' fun t h => ⟨h.1, h.2.1⟩)
        (fun t ⟨E, hdi, l, hl0⟩ => WP.mono (lNtz_ok L E hi hi' hdi hl0) fun t' P => (P.env L E).ebp)
        (CT.taintS [.ebp] (pin_ebp fun _ h => h) (by taint_decide)))
    obtain ⟨t₂, run₂, m₂, g₂, -, rd₂, wr₂⟩ := spill_ok L E
    have f₂ : Frame (spillR p) t.mem t₂.mem := by rw [m₂]; exact spill_frame p _ _ _
    refine WP.of_runBlock ⟨t₂, run₂, E.mut L (by rw [g₂, E.ebp]) (by rw [g₂, E.esp]) rd₂ wr₂
      (frame_toMut f₂ (inMut_spillR p)), by rw [g₂, hdi], l, ?_⟩
    rw [Proof.Ocb.blockAtMem_frame f₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)), hl0]
  · -- in the table: the walk, on `i` alone
    exact CT.taint [.ebp, .eax] (pin2 fun _ h => ⟨h.1.ebp, h.2.2.1⟩) (by taint_decide)

/-- The straight-line blocks of a pass with `body`, constant time from the
addresses they use: the step after `lAddr` of one block (`one`) and of the
fourth of four (`last`), from the block's address (`esi`) and
`L_{ntz(i)}`'s (`edx`), and the first three of four (`three`), from `W` and
the blocks' address. -/
structure StepCT (p : Prm) (body : List Instr) : Prop where
  one : ∀ {J : State → Prop} {B X : BitVec 32}, (∀ s, J s → s.gpr .esi = B ∧ s.gpr .edx = X) →
    CT J (.block (ofsDx ++ blockOps body ++ ([.alu .sub .ebx (imm 1)] : List Instr)))
  three : ∀ {J : State → Prop} {B : BitVec 32}, (∀ s, J s → s.gpr .ebp = p.W ∧ s.gpr .esi = B) →
    CT J (.block (stepAt 0 body ++ stepAt 1 body ++ stepAt 0 body))
  last : ∀ {J : State → Prop} {B X : BitVec 32}, (∀ s, J s → s.gpr .esi = B ∧ s.gpr .edx = X) →
    CT J (.block (ofsDx ++ blockOps body ++ ([.alu .sub .ebx (imm 4), .alu .cmp .ebx (imm 4)] : List Instr)))

theorem stepCT_xorOfs (p : Prm) : StepCT p xorOfs :=
  ⟨fun h => by exact CT.taintS [.esi, .edx] (pin2 h) (by taint_decide),
    fun h => by exact CT.taintS [.ebp, .esi] (pin2 h) (by taint_decide),
    fun h => by exact CT.taintS [.esi, .edx] (pin2 h) (by taint_decide)⟩

theorem stepCT_sealPre (p : Prm) : StepCT p (addCk ++ xorOfs) :=
  ⟨fun h => by exact CT.taintS [.esi, .edx] (pin2 h) (by taint_decide),
    fun h => by exact CT.taintS [.ebp, .esi] (pin2 h) (by taint_decide),
    fun h => by exact CT.taintS [.esi, .edx] (pin2 h) (by taint_decide)⟩

theorem stepCT_openPost (p : Prm) : StepCT p (xorOfs ++ addCk) :=
  ⟨fun h => by exact CT.taintS [.esi, .edx] (pin2 h) (by taint_decide),
    fun h => by exact CT.taintS [.ebp, .esi] (pin2 h) (by taint_decide),
    fun h => by exact CT.taintS [.esi, .edx] (pin2 h) (by taint_decide)⟩

/-- `lAddr` for block `i + 1` of a pass, and what it leaves in the registers
the block's step addresses memory with. -/
theorem lAddr_xi {p : Prm} (L : Lay p) {fC : Block → Block → Block → Block} {m i b : Nat} (hi : i < m)
    (hmn : 16 * m ≤ p.n) :
    CT (XI p fC m i b) lAddr ∧ ∀ t, XI p fC m i b t → WP isa lAddr t fun t' =>
      t'.gpr .esi = p.D + BitVec.ofNat 32 (16 * i) ∧ t'.gpr .edx = p.W + BitVec.ofNat 32 (lOff (i + 1)) := by
  have hn := L.n32
  exact ⟨lAddr_ct L (i := i + 1) (by omega_arith) (by omega_arith)
      fun t ⟨_, _, _, _, _, _, P, _⟩ => ⟨P.env, P.edi, _, P.l0⟩,
    fun t ⟨_, _, _, _, _, _, P, _⟩ =>
      WP.mono (lAddr_ok L P.env (by omega_arith) (by omega_arith) (by omega_arith) P.edi P.l0 P.tbl) fun t₁ P₁ =>
        ⟨by rw [P₁.gpr _ (by decide) (by decide) (by decide), P.esi], P₁.edx⟩⟩

/-- The blocks from `i₀ + 1` on, one at a time. -/
theorem single_ct {p : Prm} (L : Lay p) {body : List Instr} {fC : Block → Block → Block → Block}
    (hB : BodyOk body (fun b o => b ^^^ o) fC) (hct : StepCT p body) {m : Nat} (hmn : 16 * m ≤ p.n) {i₀ : Nat}
    (hi₀ : i₀ < m) : CT (XI p fC m i₀ (m - i₀)) (single body) := by
  have hn := L.n32
  unfold single
  refine (CT.loopN (fun n t => 0 < n ∧ n ≤ m ∧ XI p fC m (m - n) (m - (m - n)) t) (fun n => ?_)
    (fun n t ⟨hn0, hnm, _, _, _, _, _, hck, P, bx⟩ =>
      WP.mono (singleStep_ok L hB hck hmn (by omega_arith) P bx) fun t' ⟨P', bx', zf'⟩ =>
      ⟨hn0, by rw [eval_ne zf']; congr 1; by_cases h : n = 1 <;> simp [h] <;> omega_arith,
        fun h1 => ⟨by omega_arith, by omega_arith, _, _, _, _, _, hck, by
          rw [show m - (n - 1) = m - n + 1 by omega_arith]; exact P', by
          rw [bx']; exact congrArg _ (by omega_arith)⟩⟩) (m - i₀)).mono
    fun t h => ⟨by omega_arith, by omega_arith, by rw [show m - (m - i₀) = i₀ by omega_arith]; exact h⟩
  by_cases hn : 0 < n ∧ n ≤ m
  swap
  · exact RelCT.of_false fun _ _ h => hn ⟨h.1.1, h.1.2.1⟩
  obtain ⟨ct, hw⟩ := lAddr_xi L (fC := fC) (i := m - n) (b := m - (m - n)) (by omega_arith) hmn
  exact CT.seq (ct.mono fun _ h => h.2.2) (fun t h => hw t h.2.2) (hct.one fun _ h => h)

/-- The blocks four at a time, from block `4 k₀ + 1`. -/
theorem quad_ct {p : Prm} (L : Lay p) {body : List Instr} {fC : Block → Block → Block → Block}
    (hB : BodyOk body (fun b o => b ^^^ o) fC) (hct : StepCT p body) {m : Nat} (hmn : 16 * m ≤ p.n) {k₀ : Nat}
    (hk₀ : 4 * k₀ + 4 ≤ m) : CT (XI p fC m (4 * k₀) (m - 4 * k₀)) (quad body) := by
  have hn := L.n32
  unfold quad
  refine (CT.loopN (fun n t => 0 < n ∧ 4 * n ≤ m ∧ XI p fC m (4 * (m / 4 - n)) (m - 4 * (m / 4 - n)) t)
    (fun n => ?_)
    (fun n t ⟨hn0, hnm, _, _, _, _, _, hck, P, bx⟩ => by
      obtain ⟨t₃, run₃, P₃, b₃⟩ := quadHead_ok L hB hck hmn (k := m / 4 - n) (by omega_arith) P
      refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
      exact WP.mono (quadTail_ok L hB hck hmn (k := m / 4 - n) (by omega_arith) P₃ (by rw [b₃, bx]))
        fun t' ⟨P', bx', cf'⟩ =>
        ⟨hn0, by rw [eval_ae cf']; congr 1; by_cases h : n = 1 <;> simp [h] <;> omega_arith,
          fun h1 => ⟨by omega_arith, by omega_arith, _, _, _, _, _, hck, by
            rw [show m / 4 - (n - 1) = m / 4 - n + 1 by omega_arith]; exact P', by
            rw [bx']; exact congrArg _ (by omega_arith)⟩⟩) (m / 4 - k₀)).mono
    fun t h => ⟨by omega_arith, by omega_arith, by rw [show m / 4 - (m / 4 - k₀) = k₀ by omega_arith]; exact h⟩
  by_cases hn : 0 < n ∧ 4 * n ≤ m
  swap
  · exact RelCT.of_false fun _ _ h => hn ⟨h.1.1, h.1.2.1⟩
  obtain ⟨ct, hw⟩ := lAddr_xi L (fC := fC) (i := 4 * (m / 4 - n) + 1 + 1 + 1) (b := m - 4 * (m / 4 - n))
    (by omega_arith) hmn
  refine CT.seq (J := XI p fC m (4 * (m / 4 - n) + 1 + 1 + 1) (m - 4 * (m / 4 - n)))
    (hct.three fun t ⟨_, _, _, _, _, _, _, _, P, _⟩ => ⟨P.env.ebp, P.esi⟩)
    (fun t ⟨_, _, _, _, _, _, _, hck, P, bx⟩ => by
      obtain ⟨t₃, run₃, P₃, b₃⟩ := quadHead_ok L hB hck hmn (k := m / 4 - n) (by omega_arith) P
      exact WP.of_runBlock ⟨t₃, run₃, _, _, _, _, _, hck, P₃, by rw [b₃, bx]⟩)
    (CT.seq ct hw (hct.last fun _ h => h))

/-- A pass of `body` over the `m` whole blocks. -/
theorem pass_ct {p : Prm} (L : Lay p) {body : List Instr} {fC : Block → Block → Block → Block}
    (hB : BodyOk body (fun b o => b ^^^ o) fC) (hct : StepCT p body)
    {m : Nat} (hmn : 16 * m ≤ p.n) : CT (PassI p fC m 0) (pass body) := by
  have hn := L.n32
  unfold pass
  refine CT.seq (J := fun t => XI p fC m 0 (m - 0) t ∧ t.cf = some (decide (m - 0 < 4)))
    (CT.taintS [.ebp] (pin_ebp fun _ ⟨_, _, _, _, _, _, P⟩ => P.env.ebp) (by taint_decide))
    (fun t ⟨_, _, _, _, _, hck, P⟩ => by
      obtain ⟨t₁, run₁, Q, bx, cf⟩ := passLoad_ok L hmn P
      exact WP.of_runBlock ⟨t₁, run₁, ⟨_, _, _, _, _, hck, Q, bx⟩, cf⟩) ?_
  -- four at a time
  refine CT.seq (J := XI p fC m (4 * (m / 4)) (m - 4 * (m / 4)))
    (CT.ite (decide (m - 0 < 4)) (fun _ h => eval_b h.2) (fun _ => CT.nil) fun hb =>
      (quad_ct L hB hct hmn (k₀ := 0) (by have := of_decide_eq_false hb; omega_arith)).mono fun _ h => h.1)
    (fun t ⟨⟨_, _, _, _, _, hck, P, bx⟩, cf⟩ => WP.mono (quads_ok L hB hck hmn P bx cf) fun t' ⟨P', bx'⟩ =>
      ⟨_, _, _, _, _, hck, P', bx'⟩) ?_
  -- the rest, one at a time
  refine CT.seq (J := fun t => XI p fC m (4 * (m / 4)) (m - 4 * (m / 4)) t ∧
      t.zf = some (decide (m - 4 * (m / 4) = 0)))
    (CT.taint [.ebp] (pin_ebp fun _ ⟨_, _, _, _, _, _, P, _⟩ => P.env.ebp) (by taint_decide))
    (fun t ⟨_, _, _, _, _, hck, P, bx⟩ => by
      obtain ⟨t₁, run₁, Q, bx₁, zf₁⟩ := passTest_ok (by omega_arith) P bx
      exact WP.of_runBlock ⟨t₁, run₁, ⟨_, _, _, _, _, hck, Q, bx₁⟩, zf₁⟩) ?_
  exact CT.seq (J := fun t => t.gpr .ebp = p.W)
    (CT.ite (decide (m - 4 * (m / 4) = 0)) (fun _ h => eval_e h.2) (fun _ => CT.nil) fun hb =>
      (single_ct L hB hct hmn (i₀ := 4 * (m / 4)) (by have := of_decide_eq_false hb; omega_arith)).mono
        fun _ h => h.1)
    (fun t ⟨⟨_, _, _, _, _, hck, P, bx⟩, zf⟩ => WP.mono (tail_ok L hB hck hmn P bx zf) fun t' ⟨P', _⟩ => P'.env.ebp)
    (CT.taintS [.ebp] (pin_ebp fun _ h => h) (by taint_decide))

/-! ## The whole blocks -/

/-- What `whole` needs. -/
def WhI (p : Prm) (m : Nat) (t : State) : Prop :=
  Env p t ∧ slotv t.mem p.W nbO = BitVec.ofNat 32 m ∧ ∃ l, blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0

/-- What its passes need: that, and the table. -/
def WhT (p : Prm) (m : Nat) (t : State) : Prop :=
  Env p t ∧ slotv t.mem p.W nbO = BitVec.ofNat 32 m ∧
    ∃ l, blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0 ∧ Tbl p l m t.mem

theorem wholeIn_ct {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86 f).pre (Proof.Aes.blocksX86 f).pub fn.code)
    (nosp : NoSp fn.code) (stack : stackUse fn.code = 0) {p : Prm} (L : Lay p) {pre post : List Instr}
    {fC1 fC2 : Block → Block → Block → Block}
    (hB1 : BodyOk pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk post (fun b o => b ^^^ o) fC2)
    (hct1 : StepCT p pre) (hct2 : StepCT p post)
    {m : Nat} (hmn : 16 * m ≤ p.n) : CT (WhT p m) (wholeIn fn pre post) := by
  have hn := L.n32
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨w64 p.D, 16 * m⟩ :=
    fun h => ((L.d_w.sub_left (Region.sub_prefix hmn)).sub_right (Lay.wSub h)).symm
  -- What a pass keeps.
  have kP : ∀ {d k : Nat} {m' : Mem} {O0 l : Block} {X : Nat → Block} {ckF : Nat → Block} {t₀ t : State} {i : Nat},
      PassInv p m O0 l X (fun b o => b ^^^ o) ckF t₀ t i → d + k ≤ 2560 →
      (d + k ≤ ofsO ∨ (48 ≤ d ∧ d + k ≤ lO) ∨ (112 ≤ d ∧ d + k ≤ kO) ∨ 224 ≤ d) → t₀.mem = m' →
      ∀ r ∈ [⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩,
        ⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩, ⟨w64 p.D, 16 * m⟩],
        (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun _ h₁ h₂ _ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (by simp only [ofsO, lO, kO] at h₂ ⊢; omega_arith) h₁ (by decide)
    · exact Lay.w_w (by simp only [ofsO, lO, kO] at h₂ ⊢; omega_arith) h₁ (by decide)
    · exact Lay.w_w (by simp only [ofsO, lO, kO] at h₂ ⊢; omega_arith) h₁ (by decide)
    · exact Lay.w_w (by simp only [ofsO, lO, kO, ckO] at h₂ ⊢; omega_arith) h₁ (by decide)
    · exact dW h₁
  -- What a call keeps.
  have kC : ∀ {d k : Nat}, d + k ≤ scrO → ∀ r ∈ [⟨w64 p.D, 16 * m⟩, ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, stk p],
      (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dW (by simp only [scrO] at h; omega_arith)
    · exact Lay.w_w (.inl h) (by simp only [scrO] at h; omega_arith) (by decide)
    · exact (L.bw' (by simp only [scrO] at h; omega_arith)).symm
  have start : ∀ {fC : Block → Block → Block → Block} t, WhT p m t → ∃ t', runBlock isa passStart t = some t' ∧
      PassI p fC m 0 t' := fun t ⟨E, nb, l, hl0, hT⟩ => by
    obtain ⟨t₁, run₁, si₁, bx₁, di₁, g₁, m₁, rd₁, wr₁⟩ := passStart_ok L E nb
    exact ⟨t₁, run₁, PassI.start (E.keep (by rw [g₁ _ (by decide) (by decide) (by decide)])
      (by rw [g₁ _ (by decide) (by decide) (by decide)]) rd₁ wr₁ m₁) si₁ di₁ bx₁ (by rw [m₁]; exact hl0)
      (by rw [m₁]; exact hT)⟩
  -- `nbO` and `l0O`, across a pass.
  have nbP : ∀ {O0 l : Block} {X : Nat → Block} {ckF : Nat → Block} {t₀ t t' : State} {i i' : Nat},
      PassInv p m O0 l X (fun b o => b ^^^ o) ckF t₀ t i → PassInv p m O0 l X (fun b o => b ^^^ o) ckF t₀ t' i' →
      slotv t'.mem p.W nbO = slotv t.mem p.W nbO := fun P P' => by
    rw [slotv_eq, slotv_eq, P'.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _)
      (kP P' (by decide) (.inr (.inr (.inr (by decide)))) rfl) (by decide),
      P.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _)
      (kP P (by decide) (.inr (.inr (.inr (by decide)))) rfl) (by decide)]
  have hargs : ∀ t, WhT p m t → ∃ s₁, runBlock isa [.mov .edx (slot dataO), .mov .ebx (slot nbO)] t = some s₁ ∧
      s₁.gpr .edx = p.D ∧ s₁.gpr .ebx = BitVec.ofNat 32 m ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s₁.gpr r = t.gpr r) ∧ s₁.mem = t.mem ∧
      s₁.rd = t.rd ∧ s₁.wr = t.wr := fun t ⟨E, nb, _⟩ => by
    have hD := E.slots.data
    simp only [slotv_eq] at hD nb
    exact ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hD, nb], by gregs [hD], by gregs [nb],
      fun r _ h₂ _ h₄ => by gregs [h₂, h₄], by gmems [], by gmems [], by gmems []⟩
  unfold wholeIn
  -- The first pass.
  refine CT.seq (J := fun t => PassI p fC1 m 0 t ∧ slotv t.mem p.W nbO = BitVec.ofNat 32 m)
    (CT.taint [.ebp] (pin_ebp fun _ h => h.1.ebp) (by taint_decide))
    (fun t ⟨E, nb, l, hl0, hT⟩ => by
      obtain ⟨t₁, run₁, si₁, bx₁, di₁, g₁, m₁, rd₁, wr₁⟩ := passStart_ok L E nb
      exact WP.of_runBlock ⟨t₁, run₁, PassI.start (E.keep (by rw [g₁ _ (by decide) (by decide) (by decide)])
        (by rw [g₁ _ (by decide) (by decide) (by decide)]) rd₁ wr₁ m₁) si₁ di₁ bx₁ (by rw [m₁]; exact hl0)
        (by rw [m₁]; exact hT), by rw [m₁]; exact nb⟩) ?_
  refine CT.seq (J := WhT p m) ((pass_ct L hB1 hct1 hmn).mono fun _ h => h.1)
    (fun t ⟨⟨_, _, _, _, _, hck, P⟩, nb⟩ => WP.mono (pass_ok L hB1 hck hmn P) fun t' P' =>
      ⟨P'.env, by rw [nbP P P', nb], _, P'.l0, P'.tbl⟩) ?_
  -- The call.
  refine CT.seq (J := WhT p m) (callBlocks_ct ok ct nosp stack L
      (fun t h => ⟨h.1, DReg.d L h.1 hmn, hargs t h⟩) fun hJ => by exact CT.taint [.ebp] (pin_ebp hJ) (by taint_decide))
    (fun t h => WP.mono (callBlocks_ok ok nosp stack L h.1 (hargs t h) (DReg.d L h.1 hmn)) fun t' P => ?_) ?_
  · obtain ⟨E, nb, l, hl0, hT⟩ := h
    refine ⟨P.env, ?_, l, ?_, hT.frame P.frame (kC (by decide))⟩
    · rw [← nb]
      exact P.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _) (kC (by decide))
        (by decide)
    · rw [Proof.Ocb.blockAtMem_frame P.frame (kC (by decide)), hl0]
  -- `Offset_0` again, and the second pass.
  refine CT.seq (J := PassI p fC2 m 0) (CT.taint [.ebp] (pin_ebp fun _ h => h.1.ebp) (by taint_decide))
    (fun t ⟨E, nb, l, hl0, hT⟩ => ?_) ((pass_ct L hB2 hct2 hmn))
  obtain ⟨t₁, run₁, m₁, g₁, rd₁, wr₁⟩ := copy16_ok L E (s := o0O) (d := ofsO) (by decide) (by decide)
    (.inr (by decide))
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩] t.mem t₁.mem := by
    rw [m₁]; exact copyMem16_frame _ _ _ _ _
  have k₁ : ∀ {d k : Nat}, (d + k ≤ ofsO ∨ ofsO + 16 ≤ d) → d + k ≤ 2560 →
      ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region)], (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun h h' r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w h h' (by decide)
  have E₁ : Env p t₁ := E.mut L (by rw [g₁ _ (by decide), E.ebp]) (by rw [g₁ _ (by decide), E.esp]) rd₁ wr₁
    (frame_toMut f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  have nb₁ : slotv t₁.mem p.W nbO = BitVec.ofNat 32 m := by
    rw [← nb]
    exact f₁.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _)
      (k₁ (.inr (by decide)) (by decide)) (by decide)
  have l0₁ : blockAtMem t₁.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0 := by
    rw [Proof.Ocb.blockAtMem_frame f₁ (k₁ (.inr (by decide)) (by decide)), hl0]
  have hT₁ : Tbl p l m t₁.mem := hT.frame f₁ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact tblR_w (.inl (by decide)) (by decide)
  obtain ⟨t', run', P⟩ := start (fC := fC2) t₁ ⟨E₁, nb₁, l, l0₁, hT₁⟩
  exact WP.of_runBlock ⟨t', runBlock_app_of run₁ run', P⟩

/-- What `ltable`'s levels need: the number of blocks, kept in `W`. -/
def LtI (p : Prm) (m : Nat) (t : State) : Prop := Env p t ∧ slotv t.mem p.W nbO = BitVec.ofNat 32 m

/-- A part of `W` written, the number of blocks kept. -/
theorem LtI.mut {p : Prm} (L : Lay p) {m : Nat} {t t' : State} (h : LtI p m t) {d k : Nat}
    (hd : 288 ≤ d ∧ d + k ≤ 384) (f : Frame [⟨w64 p.W + BitVec.ofNat 64 d, k⟩] t.mem t'.mem)
    (g : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) (rd : t'.rd = t.rd) (wr : t'.wr = t.wr) :
    LtI p m t' := by
  refine ⟨h.1.mut L (by rw [g _ (by decide) (by decide) (by decide), h.1.ebp])
    (by rw [g _ (by decide) (by decide) (by decide), h.1.esp]) rd wr (frame_toMut f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact inMut_w p (.inr (.inr (.inl ⟨by omega_arith, by omega_arith⟩)))), ?_⟩
  rw [← h.2]
  exact f.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Lay.w_w (.inl (by simp only [nbO]; omega_arith)) (by decide) (by omega_arith)) (by decide)

/-- One level of `ltableFrom`: it branches on the number of blocks, and
addresses `W`. -/
theorem ltLevel_ct {p : Prm} (L : Lay p) {m j : Nat} (hm : m < 2 ^ 32) (hj : j < 5) {rest : Prog isa}
    (h₁ : CT (fun t => t.gpr .ebp = p.W) (.block [.mov .eax (slot nbO), .alu .cmp .eax (imm (2 ^ (j + 1)))]))
    (h₂ : CT (fun t => t.gpr .ebp = p.W) (.block (dbl .ebp (tblO + 16 * j) (tblO + 16 * (j + 1)))))
    (hr : CT (LtI p m) rest) :
    CT (LtI p m) (.seq (.block [.mov .eax (slot nbO), .alu .cmp .eax (imm (2 ^ (j + 1)))])
      (.ite .b (.block []) (.seq (.block (dbl .ebp (tblO + 16 * j) (tblO + 16 * (j + 1)))) rest))) := by
  have h288 : tblO = 288 := rfl
  refine CT.seq (J := fun t => LtI p m t ∧ t.cf = some (decide (m < 2 ^ (j + 1)))) (h₁.mono fun _ h => h.1.ebp)
    (fun t ⟨E, nb⟩ => ?_)
    (CT.ite _ (fun _ h => eval_b h.2) (fun _ => CT.nil) fun _ =>
      (CT.seq (J := LtI p m) (h₂.mono fun _ h => h.1.ebp) (fun t h => ?_) hr).mono fun _ h => h.1)
  · obtain ⟨t₁, run₁, cf₁, g₁, m₁, rd₁, wr₁⟩ := ltHead_ok L E hm hj nb
    exact WP.of_runBlock ⟨t₁, run₁, ⟨E.keep (g₁ _ (by decide)) (g₁ _ (by decide)) rd₁ wr₁ m₁, by rw [m₁]; exact nb⟩,
      cf₁⟩
  · obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := dblW_ok L h.1 (s := tblO + 16 * j) (d := tblO + 16 * (j + 1))
      (by omega_arith) (by omega_arith) (.inr (.inl (by omega_arith)))
    exact WP.of_runBlock ⟨t₂, run₂, h.mut L (d := tblO + 16 * (j + 1)) (k := 16) ⟨by omega_arith, by omega_arith⟩
      (by rw [m₂]; exact dblMem_frame _ _ _ _ _) g₂ rd₂ wr₂⟩

/-- `ltable`: its levels, for the public number of blocks. -/
theorem ltable_ct {p : Prm} (L : Lay p) {m : Nat} (hm : m < 2 ^ 32) : CT (LtI p m) ltable := by
  have lvl : ∀ {j : Nat}, CT (fun t => t.gpr .ebp = p.W)
      (.block (dbl .ebp (tblO + 16 * j) (tblO + 16 * (j + 1)))) →
      CT (fun t => t.gpr .ebp = p.W) (.block [.mov .eax (slot nbO), .alu .cmp .eax (imm (2 ^ (j + 1)))]) →
      j < 5 → ∀ {rest : Prog isa}, CT (LtI p m) rest →
      CT (LtI p m) (.seq (.block [.mov .eax (slot nbO), .alu .cmp .eax (imm (2 ^ (j + 1)))])
        (.ite .b (.block []) (.seq (.block (dbl .ebp (tblO + 16 * j) (tblO + 16 * (j + 1)))) rest))) :=
    fun h₂ h₁ hj _ hr => ltLevel_ct L hm hj h₁ h₂ hr
  unfold ltable
  refine CT.seq (J := LtI p m) (CT.taint [.ebp] (pin_ebp fun _ h => h.1.ebp) (by taint_decide)) (fun t h => ?_) ?_
  · obtain ⟨t₁, run₁, m₁, g₁, rd₁, wr₁⟩ := copy16_ok L h.1 (s := l0O) (d := tblO) (by decide) (by decide)
      (.inl (by decide))
    exact WP.of_runBlock ⟨t₁, run₁, h.mut L (d := tblO) (k := 16) ⟨by decide, by decide⟩
      (by rw [m₁]; exact copyMem16_frame _ _ _ _ _) (fun r h₁ _ _ => g₁ r h₁) rd₁ wr₁⟩
  simp only [ltableFrom]
  exact lvl (j := 0) (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))
    (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)) (by decide)
    (lvl (j := 1) (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))
      (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)) (by decide)
      (lvl (j := 2) (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))
        (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)) (by decide)
        (lvl (j := 3) (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))
          (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)) (by decide)
          (lvl (j := 4) (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))
            (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)) (by decide) CT.nil))))

/-- `whole`: the table, then the passes around the call. -/
theorem whole_ct {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86 f).pre (Proof.Aes.blocksX86 f).pub fn.code)
    (nosp : NoSp fn.code) (stack : stackUse fn.code = 0) {p : Prm} (L : Lay p) {pre post : List Instr}
    {fC1 fC2 : Block → Block → Block → Block}
    (hB1 : BodyOk pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk post (fun b o => b ^^^ o) fC2)
    (hct1 : StepCT p pre) (hct2 : StepCT p post)
    {m : Nat} (hmn : 16 * m ≤ p.n) : CT (WhI p m) (whole fn pre post) := by
  have hn := L.n32
  have hm : m < 2 ^ 32 := by omega_arith
  unfold whole
  refine CT.seq (J := WhT p m) ((ltable_ct L hm).mono fun _ h => ⟨h.1, h.2.1⟩)
    (fun t ⟨E, nb, l, hl0⟩ => WP.mono (ltable_ok L E hm nb hl0) fun t₁ ⟨T₁, K₁⟩ => ?_)
    (wholeIn_ct ok ct nosp stack L hB1 hB2 hct1 hct2 hmn)
  refine ⟨K₁.env L E, by rw [K₁.nb, nb], l, ?_, T₁⟩
  rw [Proof.Ocb.blockAtMem_frame K₁.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (tblR_w (.inl (by decide)) (by decide)).symm), hl0]

/-! ## The rest -/

/-- What the rest's pieces need: the environment, the rest's address in
`esi` and its length in `W + restO`. -/
def RI (p : Prm) (P : BitVec 32) (r : Nat) (t : State) : Prop :=
  Env p t ∧ t.gpr .esi = P ∧ slotv t.mem p.W restO = BitVec.ofNat 32 r ∧ RBuf p t P r

theorem padCk_ct {p : Prm} (L : Lay p) {P : BitVec 32} {r : Nat} (hr : 0 < r) (hr' : r < 16) :
    CT (RI p P r) padCk := by
  unfold padCk
  refine CT.seq (J := Env p) (padTo_ct L (.inr rfl) fun t h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun t ⟨E, si, rest, hP⟩ => WP.mono (padTo_ok L E (d := t2O) (cO := restO) hr hr' (by decide) (by decide)
      (.inr (by decide)) si rest hP.sbuf) fun t' ⟨fr, _, g, rd, wr⟩ =>
        E.mut L (by rw [g _ (by decide) (by decide) (by decide) (by decide), E.ebp])
          (by rw [g _ (by decide) (by decide) (by decide) (by decide), E.esp]) rd wr
          (frame_toMut fr fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))))
    (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide))

theorem padCk_ri {p : Prm} (L : Lay p) {P : BitVec 32} {r : Nat} (hr : 0 < r) (hr' : r < 16) {t : State}
    (h : RI p P r t) : WP isa padCk t (RI p P r) := by
  obtain ⟨E, si, rest, hP⟩ := h
  refine WP.mono (padCk_ok L E hr hr' si rest hP.sbuf) fun t' ⟨fr, _, g, rd, wr⟩ => ⟨?_, ?_, ?_, hP.of_eq wr⟩
  · exact E.mut L (by rw [g _ (by decide) (by decide) (by decide) (by decide), E.ebp])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide), E.esp]) rd wr
      (frame_toMut fr fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
        · exact inMut_w p (.inl (by decide)))
  · rw [g _ (by decide) (by decide) (by decide) (by decide), si]
  · rw [← rest]
    exact fr.readW (r := ⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> exact Lay.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)

theorem xorPad_ct {p : Prm} (L : Lay p) {P : BitVec 32} {r : Nat} : CT (RI p P r) xorPad := by
  unfold xorPad
  refine CT.seq (J := fun t => t.gpr .edi = P ∧ t.gpr .edx = p.W + BitVec.ofNat 32 tmpO ∧
      t.gpr .ecx = BitVec.ofNat 32 r)
    (CT.taint [.ebp, .esi] (pin2 fun _ h => ⟨h.1.ebp, h.2.1⟩) (by taint_decide)) (fun t ⟨E, si, rest, _⟩ => ?_)
    (xorLoop_ct (pin3 fun _ h => h))
  simp only [slotv_eq] at rest
  exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR, si, rest], by gregs [si], by gregs [E.ebp],
    by gregs [rest]⟩

theorem xorPad_ri {p : Prm} (L : Lay p) {P : BitVec 32} {r : Nat} (hr : 0 < r) (hr' : r < 16) {t : State}
    (h : RI p P r t) : WP isa xorPad t (RI p P r) := by
  obtain ⟨E, si, rest, hP⟩ := h
  refine WP.mono (xorPad_ok L E hr hr' si rest hP) fun t' ⟨m, g, rd, wr⟩ => ?_
  have fr : Frame [⟨w64 P, r⟩] t.mem t'.mem := by
    rw [m]
    exact writeBytes_frame _ _ _ (by
      simp only [Spec.Ocb.xor, List.length_zipWith, length_bytesAt, Nat.min_self]; exact Region.contains_self _ _)
  refine ⟨E.mut L (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), E.ebp])
    (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), E.esp]) rd wr (frame_toMut fr hP.inm),
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), si], ?_, hP.of_eq wr⟩
  rw [← rest]
  exact fr.readW (r := ⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩) (Region.contains_self _ _) (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact (hP.w.sub_right (Lay.wSub (by decide))).symm) (by decide)

theorem rest_ct (v : BlocksImpl) (enc : Bool) {p : Prm} (L : Lay p) {P : BitVec 32} {r : Nat} (hr : 0 < r)
    (hr' : r < 16) : CT (RI p P r) (rest (callees v) enc) := by
  unfold rest
  refine RelCT.assoc (CT.seq (J := RI p P r) (CT.seq (J := Env p) ?_ (fun t h => ?_)
    (oneCall_ct v.encOk v.encCt v.encNosp v.encStack L (.inl rfl) fun _ h => h))
    (fun t ⟨E, si, rest, hP⟩ => WP.mono (restHead_ok v L E) fun t' H => ⟨H.env, ?_, ?_, hP.of_eq H.wr⟩) ?_)
  · rw [show ([.mov .ebx (slot ctxO)] ++ xor16 .ebx 240 ofsO ++ copy16 ofsO tmpO : List Instr) =
      .mov .ebx (slot ctxO) :: (xor16 .ebx 240 ofsO ++ copy16 ofsO tmpO) from rfl]
    exact load_blk_ct L (r := .ebx) (o := ctxO) (by decide) (fun t h => ⟨h.1, h.1.slots.ctx⟩)
      (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))
      (CT.taint [.ebp, .ebx] (pin2 fun t h => ⟨Ld.reg (by decide)
        (fun s (h : RI p P r s) => h.1.ebp) t h, by obtain ⟨_, _, hv, _⟩ := h; exact hv⟩) (by taint_decide))
  · obtain ⟨t₃, run₃, E₃, -⟩ := restBlk_ok L h.1
    exact WP.of_runBlock ⟨t₃, run₃, E₃⟩
  · rw [H.gpr _ (by decide) (by decide) (by decide) (by decide), si]
  · rw [← rest]
    exact H.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)
  cases enc
  · exact CT.seq (xorPad_ct L) (fun t h => xorPad_ri L hr hr' h) (padCk_ct L hr hr')
  · exact CT.seq (padCk_ct L hr hr') (fun t h => padCk_ri L hr hr' h) (xorPad_ct L)

/-! ## `body` -/

/-- What `body` needs at its start. -/
def BI (p : Prm) (t : State) : Prop :=
  Env p t ∧ blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 o0O) = blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ∧
    blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) = 0 ∧
    blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt (ctxLstar t.mem (w64 p.K)) 0

theorem bodyHead_whi {p : Prm} (L : Lay p) {t : State} (E : Env p t) {l : Block}
    (hl0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (.block [.mov .ebx (slot lenO), .shift .shr .ebx 4, .store (at_ .ebp nbO) .ebx,
        .alu .test .ebx (.reg .ebx)]) t fun t' => WhI p (p.n / 16) t' ∧ t'.zf = some (decide (p.n / 16 = 0)) := by
  obtain ⟨t₁, run₁, m₁, zf₁, g₁, rd₁, wr₁⟩ := bodyHead_ok L E
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩] t.mem t₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.of_runBlock ⟨t₁, run₁, ⟨E.mut L (by rw [g₁ _ (by decide), E.ebp]) (by rw [g₁ _ (by decide), E.esp]) rd₁ wr₁
    (frame_toMut f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))),
    by rw [slotv_eq, m₁, Mem.readW_writeW_self32], l, ?_⟩, zf₁⟩
  rw [Proof.Ocb.blockAtMem_frame f₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)), hl0]

theorem bodyTail_ri {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (.block [.mov .esi (slot dataO), .mov .eax (slot lenO), .mov .ecx (.reg .eax), .alu .and .ecx (imm 15),
        .store (at_ .ebp restO) .ecx, .alu .sub .eax (.reg .ecx), .alu .add .esi (.reg .eax),
        .alu .test .ecx (.reg .ecx)]) t fun t' => Env p t' ∧
      t'.gpr .esi = p.D + BitVec.ofNat 32 (16 * (p.n / 16)) ∧
      slotv t'.mem p.W restO = BitVec.ofNat 32 (p.n % 16) ∧ t'.zf = some (decide (p.n % 16 = 0)) := by
  obtain ⟨t₁, run₁, si₁, zf₁, m₁, g₁, rd₁, wr₁⟩ := bodyTail_ok L E
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩] t.mem t₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact WP.of_runBlock ⟨t₁, run₁, E.mut L (by rw [g₁ _ (by decide) (by decide) (by decide), E.ebp])
    (by rw [g₁ _ (by decide) (by decide) (by decide), E.esp]) rd₁ wr₁ (frame_toMut f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))),
    si₁, by rw [slotv_eq, m₁, Mem.readW_writeW_self32], zf₁⟩

/-- The rest of `body`, if there is one. -/
theorem bodyRest_ct (v : BlocksImpl) (enc : Bool) {p : Prm} (L : Lay p) :
    CT (Env p) (.seq (.block [.mov .esi (slot dataO), .mov .eax (slot lenO), .mov .ecx (.reg .eax),
        .alu .and .ecx (imm 15), .store (at_ .ebp restO) .ecx, .alu .sub .eax (.reg .ecx), .alu .add .esi (.reg .eax),
        .alu .test .ecx (.reg .ecx)]) (.ite .e (.block []) (rest (callees v) enc))) :=
  CT.seq (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun t E => bodyTail_ri L E)
    (CT.ite _ (fun _ h => eval_e h.2.2.2) (fun _ => CT.nil) fun hb => by
      have hr : 0 < p.n % 16 := by have := of_decide_eq_false hb; omega_arith
      exact (rest_ct v enc L hr (Nat.mod_lt _ (by decide))).mono fun t h =>
        ⟨h.1, h.2.1, h.2.2.1, rbuf_tail L h.1 hr⟩)

theorem bodySeal_ct (v : BlocksImpl) {p : Prm} (L : Lay p) : CT (BI p) (body (callees v) true) := by
  have hn := L.n32
  simp only [body, ↓reduceIte]
  refine RelCT.assoc (CT.seq (J := Env p) (CT.seq (J := fun t => WhI p (p.n / 16) t ∧ t.zf = some (decide (p.n / 16 = 0)))
      (CT.taint [.ebp] (pin_ebp fun _ h => h.1.ebp) (by taint_decide)) (fun t ⟨E, _, _, hl0⟩ => bodyHead_whi L E hl0)
      (CT.ite _ (fun _ h => eval_e h.2) (fun _ => CT.nil) fun _ => ?_)) (fun t ⟨E, ho0, hck, hl0⟩ => ?_)
    (bodyRest_ct v true L))
  · exact (whole_ct v.encOk v.encCt v.encNosp v.encStack L sealPre_ok xorOfs_ok (stepCT_sealPre p) (stepCT_xorOfs p)
      (Nat.mul_div_le _ _)).mono fun _ h => h.1
  · exact WP.mono (wholeIte_ok (O0 := blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO))
      (l := ctxLstar t.mem (w64 p.K)) (G := fun m => ctxCiph m (w64 p.K) p.R)
      (ckF1 := ckOf fun i => blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * i)))
      (ckF2 := fun _ => ckOf (fun i => blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * i))) (p.n / 16))
      v.encOk v.encNosp v.encStack (fun P _ hi => P.enc hi) (fun h => ctxCiph_mut L h) sealPre_ok xorOfs_ok
      L E rfl ho0 hck hl0 (fun _ _ => rfl) rfl (fun _ _ => rfl)) fun _ Pw => Pw.env

theorem bodyOpen_ct (v : BlocksImpl) {p : Prm} (L : Lay p) : CT (BI p) (body (callees v) false) := by
  have hn := L.n32
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine RelCT.assoc (CT.seq (J := Env p) (CT.seq (J := fun t => WhI p (p.n / 16) t ∧ t.zf = some (decide (p.n / 16 = 0)))
      (CT.taint [.ebp] (pin_ebp fun _ h => h.1.ebp) (by taint_decide)) (fun t ⟨E, _, _, hl0⟩ => bodyHead_whi L E hl0)
      (CT.ite _ (fun _ h => eval_e h.2) (fun _ => CT.nil) fun _ => ?_)) (fun t ⟨E, ho0, hck, hl0⟩ => ?_)
    (bodyRest_ct v false L))
  · exact (whole_ct v.decOk v.decCt v.decNosp v.decStack L xorOfs_ok openPost_ok (stepCT_xorOfs p) (stepCT_openPost p)
      (Nat.mul_div_le _ _)).mono fun _ h => h.1
  · exact WP.mono (wholeIte_ok (O0 := blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO))
      (l := ctxLstar t.mem (w64 p.K)) (G := fun m => ctxInv m (w64 p.K) p.R) (ckF1 := fun _ => 0)
      (ckF2 := ckOf fun i => ctxInv t.mem (w64 p.K) p.R
        (blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * i)) ^^^
          offAt (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO)) (ctxLstar t.mem (w64 p.K)) (i + 1)) ^^^
        offAt (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO)) (ctxLstar t.mem (w64 p.K)) (i + 1))
      v.decOk v.decNosp v.decStack (fun P _ hi => P.dec hi) (fun h => ctxInv_mut L h) xorOfs_ok openPost_ok
      L E rfl ho0 hck hl0 (fun _ _ => rfl) rfl (fun _ _ => rfl)) fun _ Pw => Pw.env

/-! ## The tag -/

theorem tag_ct (v : BlocksImpl) {p : Prm} (L : Lay p) {d : Nat} (hd : d = tagO ∨ d = t2O) :
    CT (Env p) (tag (callees v) d) := by
  have step : ∀ {u u' : State} {a : Nat}, Env p u → a + 16 ≤ 128 →
      Frame [⟨w64 p.W + BitVec.ofNat 64 a, 16⟩] u.mem u'.mem → (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) →
      u'.rd = u.rd → u'.wr = u.wr → Env p u' := fun Eu ha f g rd wr =>
    Eu.mut L (by rw [g _ (by decide), Eu.ebp]) (by rw [g _ (by decide), Eu.esp]) rd wr (frame_toMut f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl ha))
  unfold tag
  refine CT.seq (J := Env p) (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun t E => ?_)
    (CT.seq (J := Env p) (oneCall_ct v.encOk v.encCt v.encNosp v.encStack L (.inl rfl) fun _ h => h)
      (fun t E => WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L E
        (oneBlock_ok E tmpO) (DReg.w L E (d := tmpO) (n := 1) (by decide) (.inl (by decide)))) fun _ P => P.env) ?_)
  · obtain ⟨t₁, run₁, m₁, g₁, rd₁, wr₁⟩ := copy16_ok L E (s := ckO) (d := tmpO) (by decide) (by decide)
      (.inl (by decide))
    have E₁ := step E (a := tmpO) (by decide) (by rw [m₁]; exact copyMem16_frame _ _ _ _ _) g₁ rd₁ wr₁
    obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := xor16W_ok L E₁ (s := ofsO) (d := tmpO) (by decide) (by decide)
      (.inl (by decide))
    have E₂ := step E₁ (a := tmpO) (by decide) (by rw [m₂]; exact xorMem16_frame _ _ _ _ _) g₂ rd₂ wr₂
    obtain ⟨t₃, run₃, m₃, g₃, rd₃, wr₃⟩ := xor16W_ok L E₂ (s := ldO) (d := tmpO) (by decide) (by decide)
      (.inl (by decide))
    exact WP.of_runBlock ⟨t₃, runBlock_app_of (runBlock_app_of run₁ run₂) run₃,
      step E₂ (a := tmpO) (by decide) (by rw [m₃]; exact xorMem16_frame _ _ _ _ _) g₃ rd₃ wr₃⟩
  · rcases hd with rfl | rfl
    · exact CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide)
    · exact CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide)

end VG.Proof.AesOcb.X86

end

end

/-! ### `AesOcb.X86.TagIO`, which this module and modules that import it used -/

section

/-!
# AES-OCB on x86: the tag in and out, checking it and masking the data

Untrusted: everything here is checked by Lean. `tagOut` copies the first
`tag_len` bytes of the tag at `W` to `tag` (`tagOut_ok`); `recv` copies the
received tag to `W` (`recv_ok`); `cmp` ORs the XORs of the first `tag_len`
bytes at `W` and `W + t2O` and leaves 1 at `W + okO` if the OR is 0, else 0
(`cmp_ok`); `mask` ANDs every byte of the data with `0 − ok` (`mask_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (zeros)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of toNat_ofNat32 toNat_add32 covers_off in_off
  in_left covers_left length_bytesAt LoopPre CopyPost copyLoop_ok bytesAt_succ add_ofNat_assoc32)

/-! ## The tag out and in -/

theorem tagOut_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (htw : Covers [⟨w64 p.T, p.tl⟩] s.wr) :
    WP isa tagOut s fun s' => s'.mem = writeBytes s.mem (w64 p.T) (bytesAt s.mem (w64 p.W) p.tl) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hT := E.slots.tg
  have hv := E.slots.tlen
  simp only [slotv_eq] at hT hv
  obtain ⟨s₁, run₁, di₁, dx₁, cx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .edi (.reg .ebp), .mov .edx (slot tgO), .mov .ecx (slot tlO)] s = some s₁ ∧
      s₁.gpr .edi = p.W ∧ s₁.gpr .edx = p.T ∧ s₁.gpr .ecx = BitVec.ofNat 32 p.tl ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hv, hT], by gregs [E.ebp], by gregs [hT], by gregs [hv],
      fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems [], by gmems []⟩
  unfold tagOut
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have ht := L.tl16
  have lp : LoopPre s₁ p.W p.T p.tl := ⟨di₁, dx₁, cx₁, L.tl1, by omega_arith, by have := L.ww; omega_arith, L.tw,
    by rw [rd₁, wr₁]; exact covers_prefix (covers_left E.perm.w) (by omega_arith),
    by rw [wr₁]; exact htw, (L.t_w.sub_right (Region.sub_prefix (by omega_arith))).symm⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s' P => ⟨by rw [P.mem, m₁], fun r h₁ h₂ h₃ h₄ => by
    rw [P.other r h₁ h₄ h₃ h₂, g₁ r h₂ h₃ h₄], by rw [P.rd, rd₁], by rw [P.wr, wr₁]⟩

theorem recv_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) :
    WP isa recv s fun s' => s'.mem = writeBytes s.mem (w64 p.W) (bytesAt s.mem (w64 p.T) p.tl) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hT := E.slots.tg
  have hv := E.slots.tlen
  simp only [slotv_eq] at hT hv
  obtain ⟨s₁, run₁, di₁, dx₁, cx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .edi (slot tgO), .mov .edx (.reg .ebp), .mov .ecx (slot tlO)] s = some s₁ ∧
      s₁.gpr .edi = p.T ∧ s₁.gpr .edx = p.W ∧ s₁.gpr .ecx = BitVec.ofNat 32 p.tl ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hv, hT], by gregs [hT], by gregs [E.ebp], by gregs [hv],
      fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems [], by gmems []⟩
  unfold recv
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have ht := L.tl16
  have lp : LoopPre s₁ p.T p.W p.tl := ⟨di₁, dx₁, cx₁, L.tl1, by omega_arith, L.tw, by have := L.ww; omega_arith,
    by rw [rd₁, wr₁]; exact E.perm.t, by rw [wr₁]; exact covers_prefix E.perm.w (by omega_arith),
    L.t_w.sub_right (Region.sub_prefix (by omega_arith))⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s' P => ⟨by rw [P.mem, m₁], fun r h₁ h₂ h₃ h₄ => by
    rw [P.other r h₁ h₄ h₃ h₂, g₁ r h₂ h₃ h₄], by rw [P.rd, rd₁], by rw [P.wr, wr₁]⟩

/-! ## `cmp` -/

theorem setWidth_xor_eq_zero32 (a b : Byte) : (a.setWidth 32 ^^^ b.setWidth 32 = 0#32) ↔ a = b := by
  rw [BitVec.xor_eq_zero_iff]
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth] at this
    rwa [Nat.mod_eq_of_lt (a := a.toNat) (by have := a.isLt; omega_arith),
      Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega_arith)] at this
  · intro h; rw [h]

theorem toNat_setWidth_xor32 (a b : Byte) : (a.setWidth 32 ^^^ b.setWidth 32).toNat < 256 := by
  simp only [BitVec.toNat_xor, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by have := a.isLt; omega_arith), Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega_arith)]
  exact Nat.xor_lt_two_pow (n := 8) a.isLt b.isLt

/-- `(x − 1) >> 31` is 1 if `x` is 0 and 0 if `0 < x < 256`. -/
theorem okBit32 {x : BitVec 32} (h : x.toNat < 256) :
    (x - BitVec.ofNat 32 1) >>> 31 = if x = 0#32 then BitVec.ofNat 32 1 else BitVec.ofNat 32 0 := by
  by_cases hx : x = 0#32
  · subst hx; decide
  · simp only [hx, ↓reduceIte]
    have hx' : 0 < x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hx
      · exact h0
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat]
    rw [show 2 ^ 32 - 1 % 2 ^ 32 + x.toNat = (x.toNat - 1) + 2 ^ 32 by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_arith), Nat.div_eq_of_lt (by omega_arith)]

/-- One step of `cmp`. -/
theorem cmpStep_ok {p : Prm} (L : Lay p) {u : State} (E : Env p u) {j tl : Nat} (hj : j < tl) (ht : tl ≤ 16)
    (hdi : u.gpr .edi = p.W + BitVec.ofNat 32 j) (hcx : u.gpr .ecx = BitVec.ofNat 32 (tl - j)) :
    ∃ u', runBlock isa [.movzx8 .eax (at_ .edi 0), .movzx8 .ebx (at_ .edi t2O), .alu .xor .eax (.reg .ebx),
        .alu .or .edx (.reg .eax), .alu .add .edi (imm 1), .alu .sub .ecx (imm 1)] u = some u' ∧
      u'.mem = u.mem ∧
      u'.gpr .edx = u.gpr .edx ||| ((u.mem (w64 p.W + BitVec.ofNat 64 j)).setWidth 32 ^^^
        (u.mem (w64 p.W + BitVec.ofNat 64 (t2O + j))).setWidth 32) ∧
      u'.gpr .edi = p.W + BitVec.ofNat 32 (j + 1) ∧ u'.gpr .ecx = BitVec.ofNat 32 (tl - (j + 1)) ∧
      u'.zf = some (decide (j + 1 = tl)) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .edi → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧
      u'.wr = u.wr := by
  have a0 : w64 (p.W + BitVec.ofNat 32 j + BitVec.ofNat 32 0) = w64 p.W + BitVec.ofNat 64 j := by
    rw [add_ofNat_assoc32, Nat.add_zero]; exact L.aW (by omega_arith)
  have a1 : w64 (p.W + BitVec.ofNat 32 j + BitVec.ofNat 32 t2O) = w64 p.W + BitVec.ofNat 64 (t2O + j) := by
    rw [add_ofNat_assoc32, Nat.add_comm]; exact L.aW (by simp only [t2O]; omega_arith)
  have r0 : InRegions (u.rd ++ u.wr) (w64 p.W + BitVec.ofNat 64 j) 1 := E.perm.wR (by omega_arith)
  have r1 : InRegions (u.rd ++ u.wr) (w64 p.W + BitVec.ofNat 64 (t2O + j)) 1 := E.perm.wR (by simp only [t2O]; omega_arith)
  refine ⟨_, by grun [hdi, a0, a1, r0, r1], by gmems [], by gregs [], ?_, ?_, ?_,
    fun r h₁ h₂ h₃ h₄ h₅ => by gregs [h₁, h₂, h₃, h₄, h₅], by gmems [], by gmems []⟩
  · gregs [hdi]; rw [add_ofNat_assoc32]
  · gregs [hcx]; rw [sub1_32 (by omega_arith) (by omega_arith), show tl - j - 1 = tl - (j + 1) by omega_arith]
  · gmems [hcx]
    rw [sub1_32 (by omega_arith) (by omega_arith), beq_zero32 (by omega_arith)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))

/-- `cmp`: 1 at `W + okO` if the first `tl` bytes at `W` and `W + t2O` are equal, else 0. -/
theorem cmp_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) :
    WP isa cmp s fun t => t.mem = s.mem.writeW (w64 p.W + BitVec.ofNat 64 okO)
        (if bytesAt s.mem (w64 p.W) p.tl = bytesAt s.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl then BitVec.ofNat 32 1
         else BitVec.ofNat 32 0) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  have hv := E.slots.tlen
  simp only [slotv_eq] at hv
  have h1 := L.tl1
  have h16 := L.tl16
  obtain ⟨s₁, run₁, dx₁, di₁, cx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .edx (imm 0), .mov .edi (.reg .ebp), .mov .ecx (slot tlO)] s = some s₁ ∧
      s₁.gpr .edx = 0#32 ∧ s₁.gpr .edi = p.W + BitVec.ofNat 32 0 ∧ s₁.gpr .ecx = BitVec.ofNat 32 (p.tl - 0) ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hv], by gregs [], by gregs [E.ebp]; exact (BitVec.add_zero _).symm,
      by gregs [hv, Nat.sub_zero], fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems [], by gmems []⟩
  unfold cmp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (WP.loop (M := isa) (c := .ne)
    (Q := fun u => (u.gpr .edx).toNat < 256 ∧
      (u.gpr .edx = 0#32 ↔ bytesAt s.mem (w64 p.W) p.tl = bytesAt s.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl) ∧
      u.mem = s.mem ∧ (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .edi → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr)
    (fun (k : Nat) (u : State) => ∃ j, k = p.tl - j ∧ j < p.tl ∧ u.gpr .edi = p.W + BitVec.ofNat 32 j ∧
      u.gpr .ecx = BitVec.ofNat 32 (p.tl - j) ∧ (u.gpr .edx).toNat < 256 ∧
      (u.gpr .edx = 0#32 ↔ bytesAt s.mem (w64 p.W) j = bytesAt s.mem (w64 p.W + BitVec.ofNat 64 t2O) j) ∧
      u.mem = s.mem ∧ (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .edi → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr) ?_ (p.tl - 0) _
    ⟨0, rfl, by omega_arith, di₁, cx₁, by rw [dx₁]; decide, by rw [dx₁]; simp [bytesAt], m₁,
      fun r _ _ h₃ h₄ h₅ => g₁ r h₃ h₄ h₅, rd₁, wr₁⟩) fun u hu => ?_)
  · rintro k u ⟨j, rfl, hj, di, cx, lt, iff, mem, g, rd, wr⟩
    have Eu : Env p u := E.keep (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)]) rd wr mem
    obtain ⟨u', run', mem', dx', di', cx', zf', g', rd', wr'⟩ := cmpStep_ok L Eu hj h16 di cx
    refine WP.of_runBlock ⟨u', run', ?_⟩
    rw [mem] at dx'
    have lt' : (u'.gpr .edx).toNat < 256 := by
      rw [dx', BitVec.toNat_or]; exact Nat.or_lt_two_pow (n := 8) lt (toNat_setWidth_xor32 _ _)
    have iff' : u'.gpr .edx = 0#32 ↔
        bytesAt s.mem (w64 p.W) (j + 1) = bytesAt s.mem (w64 p.W + BitVec.ofNat 64 t2O) (j + 1) := by
      rw [dx', BitVec.or_eq_zero_iff, iff, setWidth_xor_eq_zero32, bytesAt_succ, bytesAt_succ, add_ofNat_assoc]
      constructor
      · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]
      · intro h
        obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [length_bytesAt, length_bytesAt])
        exact ⟨h₁, List.head_eq_of_cons_eq h₂⟩
    have gg : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .edi → u'.gpr r = s.gpr r :=
      fun r h₁ h₂ h₃ h₄ h₅ => by rw [g' r h₁ h₂ h₃ h₄ h₅, g r h₁ h₂ h₃ h₄ h₅]
    by_cases he : j + 1 = p.tl
    · left
      refine ⟨(eval_ne zf').trans (by simp [he]), lt', ?_, by rw [mem', mem], gg, by rw [rd', rd], by rw [wr', wr]⟩
      rw [← he]; exact iff'
    · right
      exact ⟨(eval_ne zf').trans (by simp [he]), p.tl - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, di', cx', lt', iff',
        by rw [mem', mem], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · obtain ⟨lt, iff, mem, g, rd, wr⟩ := hu
    have Eu : Env p u := E.keep (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)]) rd wr mem
    have hb := okBit32 lt
    refine WP.of_runBlock ⟨_, by grun [Eu.ebp, L.aW, Eu.perm.wW], ?_, fun r h₁ h₂ h₃ h₄ h₅ => ?_, ?_, ?_⟩
    · gmems [mem, hb]
      by_cases h : u.gpr .edx = 0#32
      · simp only [h, ↓reduceIte, iff.mp h]
      · have h' : ¬ bytesAt s.mem (w64 p.W) p.tl = bytesAt s.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl :=
          fun e => h (iff.mpr e)
        simp only [h, h', ↓reduceIte]
    · gregs [h₄]; exact g r h₁ h₂ h₃ h₄ h₅
    · gmems []; exact rd
    · gmems []; exact wr

/-! ## `mask` -/

theorem mask_byte32 (b : Byte) (c : Bool) :
    ((b.setWidth 32 &&& ((0 : BitVec 32) - (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 32) else 0) = 1 from rfl,
      show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    simp

/-- `0 − ok` in every word of an SSE register. -/
def maskX (c : Bool) : BitVec 128 := if c then BitVec.allOnes 128 else 0

theorem mask_xmm (c : Bool) :
    shufDwords ((0 : BitVec 96) ++ ((0 : BitVec 32) - (if c then 1 else 0))) 0 = maskX c := by
  cases c <;> decide

theorem mask_block (v : BitVec 128) (c : Bool) : v &&& maskX c = if c then v else 0 := by
  cases c
  · simp [maskX]
  · simp only [maskX, ite_true, BitVec.and_allOnes]

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

theorem mask_add (m : Mem) (P : Addr) (c : Bool) (a b : Nat) :
    (if c then bytesAt m P (a + b) else zeros (a + b)) =
      (if c then bytesAt m P a else zeros a) ++
        (if c then bytesAt m (P + BitVec.ofNat 64 a) b else zeros b) := by
  cases c <;> simp [zeros, Proof.Ocb.bytesAt_append, ← List.replicate_append_replicate]

/-- A block written is its 16 bytes written. -/
theorem writeW_eq_writeBytes (m : Mem) (a : Addr) (v : BitVec 128) :
    m.writeW a v = writeBytes m a ((List.range 16).map fun k => v.extractLsb' (8 * k) 8) :=
  write_eq_writeBytes m a 16 v

/-- The block at `a`, or zero, written back: the 16 bytes at `a` masked. -/
theorem writeW_mask (m m' : Mem) (a : Addr) (c : Bool) :
    m'.writeW a (if c then m.readW a 128 else (0 : BitVec 128)) =
      writeBytes m' a (if c then bytesAt m a 16 else zeros 16) := by
  rw [writeW_eq_writeBytes]
  refine congrArg (writeBytes m' a) ?_
  cases c
  · simp [zeros]; decide
  · simp only [ite_true, bytesAt]
    refine List.map_congr_left fun k hk => ?_
    rw [List.mem_range] at hk
    rw [← Mem.extractLsb'_read m a (n := 16) hk]
    rfl

/-- What both loops keep: `edi` after the first `j` bytes of the data, which
are masked, and the mask in `edx` and `xmm0`. -/
structure MInv (p : Prm) (s s₁ t : State) (c : Bool) (j : Nat) : Prop where
  edi : t.gpr .edi = p.D + BitVec.ofNat 32 j
  mem : t.mem = writeBytes s.mem (w64 p.D) (if c then bytesAt s.mem (w64 p.D) j else zeros j)
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edi → t.gpr r = s₁.gpr r
  xmm0 : t.xmm .xmm0 = s₁.xmm .xmm0
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem MInv.frame {p : Prm} {s s₁ t : State} {c : Bool} {j : Nat} (h : MInv p s s₁ t c j) :
    Frame [⟨w64 p.D, j⟩] s.mem t.mem := by
  rw [h.mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)

/-- The bytes from `j` on are as they were. -/
theorem MInv.at {p : Prm} {s s₁ t : State} {c : Bool} {j i : Nat} (h : MInv p s s₁ t c j) (hi : j ≤ i)
    (hi' : i < 2 ^ 64) : t.mem (w64 p.D + BitVec.ofNat 64 i) = s.mem (w64 p.D + BitVec.ofNat 64 i) :=
  h.frame (w64 p.D + BitVec.ofNat 64 i) fun r hr hcon => by
    simp only [List.mem_singleton] at hr; subst hr
    simp only [Region.Contains, Mem.sub_ofNat_toNat (w64 p.D) hi'] at hcon; omega_arith

theorem MInv.readW {p : Prm} {s s₁ t : State} {c : Bool} {j : Nat} (h : MInv p s s₁ t c j)
    (hj : j + 16 < 2 ^ 64) :
    t.mem.readW (w64 p.D + BitVec.ofNat 64 j) 128 = s.mem.readW (w64 p.D + BitVec.ofNat 64 j) 128 := by
  refine Mem.readW_congr fun k hk => ?_
  rw [add_ofNat_assoc]
  exact h.at (by omega_arith) (by omega_arith)

/-- One step of `maskBlocks`. -/
theorem maskBlock_ok {p : Prm} (L : Lay p) {u : State} {j w : Nat} {c : Bool} (hj : j + 16 ≤ p.n) (hw : 0 < w)
    (hw' : w < 2 ^ 32) (hdi : u.gpr .edi = p.D + BitVec.ofNat 32 j) (hax : u.gpr .eax = BitVec.ofNat 32 w)
    (hx0 : u.xmm .xmm0 = maskX c)
    (r : InRegions (u.rd ++ u.wr) (w64 p.D + BitVec.ofNat 64 j) 16)
    (w16 : InRegions u.wr (w64 p.D + BitVec.ofNat 64 j) 16) :
    ∃ u', runBlock isa [.movdquLoad .xmm1 (at_ .edi 0), .xop (.bin .pand .xmm1 .xmm0),
        .movdquStore (at_ .edi 0) .xmm1, .alu .add .edi (imm 16), .alu .sub .eax (imm 1)] u = some u' ∧
      u'.mem = u.mem.writeW (w64 p.D + BitVec.ofNat 64 j)
        (if c then u.mem.readW (w64 p.D + BitVec.ofNat 64 j) 128 else (0 : BitVec 128)) ∧
      u'.gpr .edi = p.D + BitVec.ofNat 32 (j + 16) ∧ u'.gpr .eax = BitVec.ofNat 32 (w - 1) ∧
      u'.zf = some (decide (w = 1)) ∧ u'.xmm .xmm0 = u.xmm .xmm0 ∧
      (∀ r, r ≠ .eax → r ≠ .edi → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  have hn := L.n32
  have a0 : w64 (p.D + BitVec.ofNat 32 j + BitVec.ofNat 32 0) = w64 p.D + BitVec.ofNat 64 j := by
    rw [add_ofNat_assoc32, Nat.add_zero]; exact w64_add (by have := L.dw; omega_arith)
  refine ⟨_, by srun [hdi, a0, r, w16], by smems [hdi, a0, hx0, eval_pand, mask_block], ?_, ?_, ?_, by smems [],
    fun r h₁ h₂ => by sregs [h₁, h₂], by smems [], by smems []⟩
  · sregs [hdi]; rw [add_ofNat_assoc32]
  · sregs [hax]; rw [sub1_32 (by omega_arith) (by omega_arith)]
  · smems [hax]
    rw [sub1_32 (by omega_arith) (by omega_arith), beq_zero32 (by omega_arith)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))

/-- One step of `maskBytes`. -/
theorem maskStep_ok {p : Prm} (L : Lay p) {u : State} {j w : Nat} {c : Bool} (hj : j < p.n) (hw : 0 < w)
    (hw' : w < 2 ^ 32) (hdi : u.gpr .edi = p.D + BitVec.ofNat 32 j) (hcx : u.gpr .ecx = BitVec.ofNat 32 w)
    (hdx : u.gpr .edx = 0 - (if c then 1 else 0))
    (r : InRegions (u.rd ++ u.wr) (w64 p.D + BitVec.ofNat 64 j) 1) (w1 : InRegions u.wr (w64 p.D + BitVec.ofNat 64 j) 1) :
    ∃ u', runBlock isa [.movzx8 .eax (at_ .edi 0), .alu .and .eax (.reg .edx), .store8 (at_ .edi 0) .al,
        .alu .add .edi (imm 1), .alu .sub .ecx (imm 1)] u = some u' ∧
      u'.mem = u.mem.writeW (w64 p.D + BitVec.ofNat 64 j)
        ((if c then u.mem (w64 p.D + BitVec.ofNat 64 j) else 0 : Byte)) ∧
      u'.gpr .edi = p.D + BitVec.ofNat 32 (j + 1) ∧ u'.gpr .ecx = BitVec.ofNat 32 (w - 1) ∧
      u'.zf = some (decide (w = 1)) ∧ u'.xmm = u.xmm ∧
      (∀ r, r ≠ .eax → r ≠ .edi → r ≠ .ecx → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  have hn := L.n32
  have a0 : w64 (p.D + BitVec.ofNat 32 j + BitVec.ofNat 32 0) = w64 p.D + BitVec.ofNat 64 j := by
    rw [add_ofNat_assoc32, Nat.add_zero]; exact w64_add (by have := L.dw; omega_arith)
  refine ⟨_, by grun [hdi, a0, r, w1], by gmems [hdx, mask_byte32], ?_, ?_, ?_, by smems [],
    fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  · gregs [hdi]; rw [add_ofNat_assoc32]
  · gregs [hcx]; rw [sub1_32 (by omega_arith) (by omega_arith)]
  · gmems [hcx]
    rw [sub1_32 (by omega_arith) (by omega_arith), beq_zero32 (by omega_arith)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))

/-- The blocks: from `j = 16 i`, with `n / 16 − i` blocks left in `eax`, to
`16 (n / 16)`. -/
theorem maskBlocks_wp {p : Prm} (L : Lay p) {s s₁ t : State} {c : Bool} {i : Nat}
    (hD : Covers [⟨w64 p.D, p.n⟩] (s.rd ++ s.wr)) (hDw : Covers [⟨w64 p.D, p.n⟩] s.wr)
    (hx0 : s₁.xmm .xmm0 = maskX c) (hi : i < p.n / 16) (ht : MInv p s s₁ t c (16 * i))
    (hax : t.gpr .eax = BitVec.ofNat 32 (p.n / 16 - i)) (hcx : t.gpr .ecx = s₁.gpr .ecx) :
    WP isa maskBlocks t fun t' => MInv p s s₁ t' c (16 * (p.n / 16)) ∧ t'.gpr .ecx = s₁.gpr .ecx := by
  have hn := L.n32
  have hd := L.dw
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = p.n / 16 - i ∧ i < p.n / 16 ∧ MInv p s s₁ t c (16 * i) ∧
      t.gpr .eax = BitVec.ofNat 32 (p.n / 16 - i) ∧ t.gpr .ecx = s₁.gpr .ecx) ?_ (p.n / 16 - i) t
    ⟨i, rfl, hi, ht, hax, hcx⟩
  rintro k t ⟨i, rfl, hi, ht, hax, hcx⟩
  have hin : 16 * i + 16 ≤ p.n := by omega_arith
  obtain ⟨t', run', mem', di', ax', zf', x0', g', rd', wr'⟩ := maskBlock_ok L (c := c) hin
    (show 0 < p.n / 16 - i by omega_arith) (by omega_arith) ht.edi hax (by rw [ht.xmm0, hx0])
    (by rw [ht.rd, ht.wr]; exact in_off hD (by omega_arith) (by omega_arith))
    (by rw [ht.wr]; exact in_off hDw (by omega_arith) (by omega_arith))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hmem : t'.mem = writeBytes s.mem (w64 p.D)
      (if c then bytesAt s.mem (w64 p.D) (16 * (i + 1)) else zeros (16 * (i + 1))) := by
    rw [mem', ht.readW (by omega_arith), ht.mem, writeW_mask, show 16 * (i + 1) = 16 * i + 16 by omega_arith, mask_add,
      ← writeBytes_append _ _ _ _ (by rw [length_mask, length_mask]; omega_arith), length_mask]
  have e1 : p.n / 16 - i - 1 = p.n / 16 - (i + 1) := by omega_arith
  have hz : t'.zf = some (decide (i + 1 = p.n / 16)) := by
    rw [zf']; exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  have ht' : MInv p s s₁ t' c (16 * (i + 1)) :=
    ⟨by rw [di', show 16 * (i + 1) = 16 * i + 16 by omega_arith], hmem,
      fun r h₁ h₂ h₃ => by rw [g' r h₁ h₃, ht.keep r h₁ h₂ h₃], by rw [x0', ht.xmm0], by rw [rd', ht.rd],
      by rw [wr', ht.wr]⟩
  have hcx' : t'.gpr .ecx = s₁.gpr .ecx := by rw [g' _ (by decide) (by decide), hcx]
  by_cases he : i + 1 = p.n / 16
  · left
    exact ⟨(eval_ne hz).trans (by simp [he]), by rw [← he]; exact ht', hcx'⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), p.n / 16 - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, ht',
      by rw [ax', e1], hcx'⟩

/-- The last bytes: from `j < n` to `n`, with `n − j` left in `ecx`. -/
theorem maskBytes_wp {p : Prm} (L : Lay p) {s s₁ t : State} {c : Bool} {j : Nat}
    (hD : Covers [⟨w64 p.D, p.n⟩] (s.rd ++ s.wr)) (hDw : Covers [⟨w64 p.D, p.n⟩] s.wr)
    (hdx : s₁.gpr .edx = 0 - (if c then 1 else 0)) (hj : j < p.n) (ht : MInv p s s₁ t c j)
    (hcx : t.gpr .ecx = BitVec.ofNat 32 (p.n - j)) :
    WP isa maskBytes t fun t' => MInv p s s₁ t' c p.n := by
  have hn := L.n32
  have hd := L.dw
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = p.n - j ∧ j < p.n ∧ MInv p s s₁ t c j ∧
      t.gpr .ecx = BitVec.ofNat 32 (p.n - j)) ?_ (p.n - j) t ⟨j, rfl, hj, ht, hcx⟩
  rintro k t ⟨j, rfl, hj, ht, hcx⟩
  obtain ⟨t', run', mem', di', cx', zf', x', g', rd', wr'⟩ := maskStep_ok L (c := c) hj
    (show 0 < p.n - j by omega_arith) (by omega_arith) ht.edi hcx
    (by rw [ht.keep _ (by decide) (by decide) (by decide), hdx])
    (by rw [ht.rd, ht.wr]; exact in_off hD (by omega_arith) (by omega_arith))
    (by rw [ht.wr]; exact in_off hDw (by omega_arith) (by omega_arith))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hmem : t'.mem = writeBytes s.mem (w64 p.D) (if c then bytesAt s.mem (w64 p.D) (j + 1) else zeros (j + 1)) := by
    rw [mem', ht.at (Nat.le_refl _) (by omega_arith), ht.mem, mask_succ,
      writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega_arith), length_mask]
  have hz : t'.zf = some (decide (j + 1 = p.n)) := by
    rw [zf']; exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  have ht' : MInv p s s₁ t' c (j + 1) :=
    ⟨di', hmem, fun r h₁ h₂ h₃ => by rw [g' r h₁ h₃ h₂, ht.keep r h₁ h₂ h₃], by rw [x', ht.xmm0], by rw [rd', ht.rd],
      by rw [wr', ht.wr]⟩
  by_cases he : j + 1 = p.n
  · left
    exact ⟨(eval_ne hz).trans (by simp [he]), by rw [← he]; exact ht'⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), p.n - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, ht',
      by rw [cx', show p.n - j - 1 = p.n - (j + 1) by omega_arith]⟩

/-- The head of `mask`: the data in `edi`, `0 − ok` in `edx` and in every
word of `xmm0`, the whole blocks in `eax` and the bytes after them in `ecx`. -/
theorem maskHead_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {c : Bool}
    (hok : slotv s.mem p.W okO = if c then BitVec.ofNat 32 1 else BitVec.ofNat 32 0) :
    ∃ s₁, runBlock isa [.mov .edi (slot dataO), .mov .ecx (slot lenO), .mov .edx (imm 0),
        .alu .sub .edx (slot okO), .xop (.movd .xmm0 .edx), .xop (.pshufd .xmm0 .xmm0 0), .mov .eax (.reg .ecx),
        .shift .shr .eax 4, .alu .and .ecx (imm 15), .alu .test .eax (.reg .eax)] s = some s₁ ∧
      s₁.gpr .edi = p.D + BitVec.ofNat 32 0 ∧ s₁.gpr .ecx = BitVec.ofNat 32 (p.n % 16) ∧
      s₁.gpr .edx = 0 - (if c then 1 else 0) ∧ s₁.gpr .eax = BitVec.ofNat 32 (p.n / 16 - 0) ∧
      s₁.zf = some (decide (p.n / 16 = 0)) ∧ s₁.xmm .xmm0 = maskX c ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
  have hn := L.n32
  have hD := E.slots.data
  have hl := E.slots.len
  simp only [slotv_eq] at hD hl hok
  have hdx : (0 : BitVec 32) - (if c then BitVec.ofNat 32 1 else BitVec.ofNat 32 0) = 0 - (if c then 1 else 0) := by
    cases c <;> rfl
  refine ⟨_, by srun [E.ebp, L.aW, E.perm.wR, hD, hl, hok], by sregs [hD]; exact (BitVec.add_zero _).symm,
    ?_, by sregs [hok]; exact hdx, by sregs [hl, Proof.AesGcm.X86.shr4 hn, Nat.sub_zero], ?_, ?_,
    fun r h₁ h₂ h₃ h₄ => by sregs [h₁, h₂, h₃, h₄], by smems [], by smems [], by smems []⟩
  · sregs [hl]
    exact (Proof.AesGcm.X86.and15 _).trans (by rw [toNat_ofNat32 hn])
  · smems [hl, Proof.AesGcm.X86.shr4 hn, BitVec.and_self, beq_zero32 (show p.n / 16 < 2 ^ 32 by omega_arith)]
  · smems [hok, hdx]; exact mask_xmm c

/-- Every byte of the data ANDed with `0 − ok`, for `ok` (at `W + okO`) 1 or
0: its whole blocks, then the rest. -/
theorem mask_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {c : Bool}
    (hok : slotv s.mem p.W okO = if c then BitVec.ofNat 32 1 else BitVec.ofNat 32 0) :
    WP isa mask s fun s' => s'.mem = writeBytes s.mem (w64 p.D) (if c then bytesAt s.mem (w64 p.D) p.n else zeros p.n) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hn := L.n32
  obtain ⟨s₁, run₁, di₁, cx₁, dx₁, ax₁, zf₁, x0₁, g₁, m₁, rd₁, wr₁⟩ := maskHead_ok L E hok
  have hD : Covers [⟨w64 p.D, p.n⟩] (s.rd ++ s.wr) := covers_left E.perm.d
  have inv₀ : MInv p s s₁ s₁ c (16 * 0) :=
    ⟨di₁, by rw [m₁]; cases c <;> simp [bytesAt, zeros, writeBytes_nil], fun _ _ _ _ => rfl, rfl, rd₁, wr₁⟩
  have fin : ∀ {t : State}, MInv p s s₁ t c p.n →
      t.mem = writeBytes s.mem (w64 p.D) (if c then bytesAt s.mem (w64 p.D) p.n else zeros p.n) ∧
        (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr :=
    fun ht => ⟨ht.mem, fun r h₁ h₂ h₃ h₄ => by rw [ht.keep r h₁ h₂ h₄, g₁ r h₁ h₂ h₃ h₄], ht.rd, ht.wr⟩
  -- The blocks.
  have words : WP isa (.ite .e (.block []) maskBlocks) s₁ fun t =>
      MInv p s s₁ t c (16 * (p.n / 16)) ∧ t.gpr .ecx = s₁.gpr .ecx := by
    refine WP.ite (decide (p.n / 16 = 0)) (eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
    · rw [of_decide_eq_true hb]; exact ⟨inv₀, rfl⟩
    · exact maskBlocks_wp L hD E.perm.d x0₁ (Nat.pos_of_ne_zero (of_decide_eq_false hb)) inv₀ ax₁ rfl
  unfold mask
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono words fun t ⟨ht, hcx⟩ => ?_)
  -- The rest.
  have cx : t.gpr .ecx = BitVec.ofNat 32 (p.n - 16 * (p.n / 16)) := by
    rw [hcx, cx₁]; exact congrArg _ (by omega_arith)
  obtain ⟨t₁, run₂, zf₂, g₂, m₂, x₂, rd₂, wr₂⟩ : ∃ t₁, runBlock isa [.alu .test .ecx (.reg .ecx)] t = some t₁ ∧
      t₁.zf = some (decide (16 * (p.n / 16) = p.n)) ∧ t₁.gpr = t.gpr ∧ t₁.mem = t.mem ∧ t₁.xmm = t.xmm ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by grun [], ?_, by gmems [], by gmems [], by smems [], by gmems [], by gmems []⟩
    gmems [cx, BitVec.and_self, beq_zero32 (show p.n - 16 * (p.n / 16) < 2 ^ 32 by omega_arith)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  have ht₁ : MInv p s s₁ t₁ c (16 * (p.n / 16)) :=
    ⟨by rw [g₂, ht.edi], by rw [m₂, ht.mem], fun r h₁ h₂ h₃ => by rw [g₂, ht.keep r h₁ h₂ h₃],
      by rw [x₂, ht.xmm0], by rw [rd₂, ht.rd], by rw [wr₂, ht.wr]⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₂, ?_⟩)
  refine WP.ite (decide (16 * (p.n / 16) = p.n)) (eval_e zf₂) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have e := of_decide_eq_true hb
    rw [e] at ht₁; exact fin ht₁
  · exact WP.mono (maskBytes_wp L hD E.perm.d dx₁ (by have := of_decide_eq_false hb; omega_arith) ht₁
      (by rw [g₂, cx])) fun t' ht' => fin ht'

end VG.Proof.AesOcb.X86

end

end

/-!
# AES-OCB on x86: `vg_aes_ocb_seal` and `vg_aes_ocb_open` in constant time

Untrusted: everything here is checked by Lean. `front` is its pieces in
sequence, each started from what the pieces before it leave (`front_ct`);
then the copies of the tag, the comparison and the mask, which address `W`,
the tag and the data, their addresses and lengths loaded from their slots
(`seal_ct`, `open_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop restore)
open VG.Proof.AesGcm.X86 (CT w64 slotv slotv_eq copyLoop_ct length_bytesAt)

/-- `front`: the entry, the setup, `Offset_0`, `HASH`, the data and the tag. -/
theorem front_ct (v : BlocksImpl) (enc : Bool) (p : Prm) {d : Nat} (hd : d = tagO ∨ d = t2O)
    (hbody : Lay p → CT (BI p) (body (callees v) enc))
    (hbw : Lay p → ∀ t, BI p t → WP isa (body (callees v) enc) t (Env p)) :
    CT (fun s => onePre s ∧ prmOf s = p) (front (callees v) enc d) := by
  by_cases hex : ∃ s, onePre s ∧ prmOf s = p
  swap
  · exact RelCT.of_false fun s _ h => hex ⟨s, h.1⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have L : Lay p := hzp ▸ lay_of hz
  have kL : ∀ {m m' : Mem}, Frame (mutR p) m m' → ctxLstar m' (w64 p.K) = ctxLstar m (w64 p.K) := fun h => lstar_mut L h
  unfold front
  -- The entry.
  refine CT.seq (J := Env p) (entry_ct p) (fun s ⟨h, hp⟩ => WP.mono (entry_ok h) fun _ En => hp ▸ En.env) ?_
  -- The setup.
  refine CT.seq (J := fun t => Env p t ∧ blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) = 0 ∧
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt (ctxLstar t.mem (w64 p.K)) 0)
    (setup_ct L fun _ h => h) (fun t E => ?_) ?_
  · obtain ⟨t₂, run₂, P₂⟩ := setup_ok L E
    have f₂ : Frame (mutR p) t.mem t₂.mem := P₂.frame.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp
    exact WP.of_runBlock ⟨t₂, run₂, E.mut L (by rw [P₂.gpr _ (by decide) (by decide) (by decide) (by decide), E.ebp])
      (by rw [P₂.gpr _ (by decide) (by decide) (by decide) (by decide), E.esp]) P₂.rd P₂.wr f₂, P₂.ck,
      by rw [P₂.l0, kL f₂]⟩
  -- `Offset_0`.
  refine CT.seq (J := BI p) (nonce_ct v L fun _ h => h.1) (fun t ⟨E, ck, l0⟩ => WP.mono (nonce_ok v L E)
    fun t' P => ⟨P.env, by rw [P.o0, P.ofs], by rw [P.keep (by decide) (by decide), ck],
      by rw [P.keep (by decide) (by decide), l0, kL (wR_mut P.frame)]⟩) ?_
  -- `HASH`.
  have kH : ∀ {m m' : Mem}, Frame (hashR p) m m' → ∀ {d : Nat},
      (d + 16 ≤ 48 ∨ (64 ≤ d ∧ d + 16 ≤ 96) ∨ (176 ≤ d ∧ d + 16 ≤ 220) ∨ (224 ≤ d ∧ d + 16 ≤ 264)) →
      blockAtMem m' (w64 p.W + BitVec.ofNat 64 d) = blockAtMem m (w64 p.W + BitVec.ofNat 64 d) :=
    fun {m m'} F {d} hd => Proof.Ocb.blockAtMem_frame F fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Lay.w_w (by simp only [sumO]; omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact Lay.w_w (by simp only [lO]; omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact Lay.w_w (by simp only [ohO]; omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact Lay.w_w (by simp only [kO]; omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact Lay.w_w (by simp only [hlO]; omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact Lay.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)
      · exact (L.bw' (by omega_using [hd])).symm
  refine CT.seq (J := BI p) ((hash_ct v L).mono fun t ⟨E, _, _, l0⟩ => ⟨_, _, _, ⟨L, rfl, rfl, rfl⟩, E, l0⟩)
    (fun t ⟨E, o0, ck, l0⟩ => WP.mono (hash_ok v ⟨L, rfl, rfl, rfl⟩ E l0) fun t' ⟨E', F, _, _, _⟩ =>
      ⟨E', by rw [kH F (by decide), kH F (by decide), o0], by rw [kH F (by decide), ck],
        by rw [kH F (by decide), l0, kL (wR_mut (hashR_wR F))]⟩) ?_
  -- The data and the tag.
  exact CT.seq (J := Env p) (hbody L) (hbw L) (tag_ct v L hd)

/-! ## The tag out and in, the comparison and the mask -/

theorem tagOut_ct {p : Prm} (L : Lay p) : CT (Env p) tagOut := by
  unfold tagOut
  refine CT.seq (J := fun t => t.gpr .edi = p.W ∧ t.gpr .edx = p.T ∧ t.gpr .ecx = BitVec.ofNat 32 p.tl)
    (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun t E => ?_) (copyLoop_ct (pin3 fun _ h => h))
  have hT := E.slots.tg
  have hv := E.slots.tlen
  simp only [slotv_eq] at hT hv
  exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hv, hT], by gregs [E.ebp], by gregs [hT], by gregs [hv]⟩

theorem recv_ct {p : Prm} (L : Lay p) : CT (Env p) recv := by
  unfold recv
  refine CT.seq (J := fun t => t.gpr .edi = p.T ∧ t.gpr .edx = p.W ∧ t.gpr .ecx = BitVec.ofNat 32 p.tl)
    (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun t E => ?_) (copyLoop_ct (pin3 fun _ h => h))
  have hT := E.slots.tg
  have hv := E.slots.tlen
  simp only [slotv_eq] at hT hv
  exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hv, hT], by gregs [hT], by gregs [E.ebp], by gregs [hv]⟩

theorem cmp_ct {p : Prm} (L : Lay p) : CT (Env p) cmp := by
  unfold cmp
  refine CT.seq (J := fun t => t.gpr .ebp = p.W ∧ t.gpr .edi = p.W ∧ t.gpr .ecx = BitVec.ofNat 32 p.tl)
    (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun t E => ?_)
    (CT.taint [.ebp, .edi, .ecx] (pin3 fun _ h => h) (by taint_decide))
  have hv := E.slots.tlen
  simp only [slotv_eq] at hv
  exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hv], by gregs [E.ebp], by gregs [E.ebp], by gregs [hv]⟩

theorem mask_ct {p : Prm} (L : Lay p) : CT (Env p) mask := by
  unfold mask
  refine load_ct L (r := .edi) (o := dataO) (by decide) (fun t E => ⟨E, E.slots.data⟩)
    (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)) ?_
  refine load_ct L (r := .ecx) (o := lenO) (by decide)
    (fun t h => ⟨Ld.env (by decide) (by decide) (fun _ h => h) t h, (Ld.env (by decide) (by decide) (fun _ h => h) t h).slots.len⟩)
    (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)) ?_
  exact CT.taintS [.ebp, .edi, .ecx] (pin3 fun t h => ⟨Ld.reg (by decide) (fun s h =>
      Ld.reg (by decide) (fun s (h : Env p s) => h.ebp) s h) t h,
    Ld.reg (by decide) (fun s h => by obtain ⟨_, _, hv, _⟩ := h; exact hv) t h,
    by obtain ⟨_, _, hv, _⟩ := h; exact hv⟩) (by taint_decide)

/-! ## The functions -/

theorem prmOf_eq {s₁ s₂ : State} (h : onePub s₁ s₂) : prmOf s₁ = prmOf s₂ := by
  obtain ⟨hsp, ha⟩ := h
  simp only [prmOf, hsp, ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide)]

theorem seal_ct (v : BlocksImpl) : ConstantTime isa sealX86.pre sealX86.pub («seal» (callees v)) := by
  refine CT.constantTime prmOf (fun _ _ _ _ h => prmOf_eq h) fun p => ?_
  by_cases hex : ∃ s, sealX86.pre s ∧ prmOf s = p
  swap
  · exact RelCT.of_false fun s _ h => hex ⟨s, h.1⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have L : Lay p := hzp ▸ lay_of (onePre_seal hz)
  unfold «seal»
  refine CT.seq (J := fun t => Env p t ∧ Covers [⟨w64 p.T, p.tl⟩] t.wr)
    ((front_ct v true p (.inl rfl) (fun L => bodySeal_ct v L) fun L t ⟨E, o0, ck, l0⟩ =>
      WP.mono (bodySeal_ok v L E rfl o0 ck l0) fun _ B => B.env).mono fun s ⟨h, hp⟩ => ⟨onePre_seal h, hp⟩)
    (fun s ⟨h, hp⟩ => WP.mono (sealFront_ok v (onePre_seal h)) fun _ ⟨F, _⟩ => hp ▸ ⟨F.env, by
      rw [F.wr]; exact covers_of_mem (r := tagR s) (by rw [h.2.1]; simp)⟩) ?_
  refine CT.seq (J := fun t => t.gpr .ebp = p.W) ((tagOut_ct L).mono fun _ h => h.1)
    (fun t ⟨E, hT⟩ => WP.mono (tagOut_ok L E hT) fun _ ⟨_, g, _⟩ => by
      rw [g _ (by decide) (by decide) (by decide) (by decide), E.ebp])
    (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))

theorem open_ct (v : BlocksImpl) : ConstantTime isa openX86.pre openX86.pub («open» (callees v)) := by
  refine CT.constantTime prmOf (fun _ _ _ _ h => prmOf_eq h) fun p => ?_
  by_cases hex : ∃ s, openX86.pre s ∧ prmOf s = p
  swap
  · exact RelCT.of_false fun s _ h => hex ⟨s, h.1⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have L : Lay p := hzp ▸ lay_of (onePre_open hz)
  unfold «open»
  refine CT.seq (J := Env p)
    ((front_ct v false p (.inr rfl) (fun L => bodyOpen_ct v L) fun L t ⟨E, o0, ck, l0⟩ =>
      WP.mono (bodyOpen_ok v L E rfl o0 ck l0) fun _ B => B.env).mono fun s ⟨h, hp⟩ => ⟨onePre_open h, hp⟩)
    (fun s ⟨h, hp⟩ => WP.mono (openFront_ok v (onePre_open h) []) fun _ ⟨F, _⟩ => hp ▸ F.env) ?_
  -- The received tag.
  refine CT.seq (J := Env p) (recv_ct L) (fun t E => WP.mono (recv_ok L E) fun t' ⟨m, g, rd, wr⟩ => ?_) ?_
  · have ht := L.tl16
    exact E.mut L (by rw [g _ (by decide) (by decide) (by decide) (by decide), E.ebp])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide), E.esp]) rd wr
      (frame_toMut (rs := [⟨w64 p.W, p.tl⟩]) (by
        rw [m]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _))
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ⟨wA p.W, by simp, Region.sub_prefix (by omega_using [ht])⟩)
  -- The comparison.
  refine CT.seq (J := fun t => Env p t ∧ ∃ c : Bool,
      slotv t.mem p.W okO = if c then BitVec.ofNat 32 1 else BitVec.ofNat 32 0) (cmp_ct L)
    (fun t E => WP.mono (cmp_ok L E) fun t' ⟨m, g, rd, wr⟩ => ⟨?_, decide (bytesAt t.mem (w64 p.W) p.tl =
      bytesAt t.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl), by
        rw [slotv_eq, m, Mem.readW_writeW_self32]; simp only [decide_eq_true_eq]⟩) ?_
  · have f : Frame [⟨w64 p.W + BitVec.ofNat 64 okO, 4⟩] t.mem t'.mem := by
      rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    exact E.mut L (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), E.ebp])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), E.esp]) rd wr
      (frame_toMut f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  -- The mask, and the result.
  refine CT.seq (J := fun t => t.gpr .ebp = p.W) ((mask_ct L).mono fun _ h => h.1)
    (fun t ⟨E, c, hok⟩ => WP.mono (mask_ok L E hok) fun _ ⟨_, g, _⟩ => by
      rw [g _ (by decide) (by decide) (by decide) (by decide), E.ebp])
    (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))

end VG.Proof.AesOcb.X86

end

end

/-! ### `AesOcb.X86.Verified`, which only this module used -/

section

/-! ### `AesOcb.X86.Seal`, which only this module used -/

section

/-!
# AES-OCB on x86: `vg_aes_ocb_seal` and `vg_aes_ocb_open`

Untrusted: everything here is checked by Lean. `seal` is `front` (the
ciphertext and the tag at `W`), the copy of the tag to `tag` (`tagOut`) and
`restore` (`seal_wp`); `open` is `front` (the plaintext and the tag at
`W + t2O`), the received tag copied to `W` (`recv`), their comparison
(`cmp`), the mask of the data (`mask`), and `ok` in `eax` before `restore`
(`open_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (zeros)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot restore)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq SavedAt exit_ok covers_left length_bytesAt bytesAt_writeBytes_self
  writeBytes_frame')

/-- The return address misses what `front` writes. -/
theorem ret_front {p : Prm} (L : Lay p) : ∀ r ∈ entryR p :: mutR p, (⟨w64 p.SP, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact L.retW.sub_right (Lay.wSub (by decide))
  · exact L.retW.sub_right (Region.sub_prefix (by decide))
  · exact L.retW.sub_right (Lay.wSub (by decide))
  · exact L.retW.sub_right (Lay.wSub (by decide))
  · exact L.retW.sub_right (Lay.wSub (by decide))
  · exact Proof.AesGcm.X86.ret_below L.sp
  · exact L.retD

/-- `vg_aes_ocb_seal`. -/
theorem seal_wp (v : BlocksImpl) {s : State} (h : sealPre s) :
    WP isa («seal» (callees v)) s fun s' => abiPreserved s s' ∧ sealX86.post s s' := by
  obtain h₁ := onePre_seal h
  obtain L := lay_of h₁
  obtain hTw : Covers [tagR s] s.wr := covers_of_mem (by rw [h.2.1]; simp)
  unfold «seal»
  refine WP.seq (WP.mono (sealFront_ok v h₁) fun s₅ ⟨F, out⟩ => ?_)
  -- The copy of the tag.
  refine WP.seq (WP.mono (tagOut_ok L F.env (by rw [F.wr]; exact hTw)) fun s₆ ⟨m₆, g₆, rd₆, wr₆⟩ => ?_)
  obtain f₆ : Frame [⟨w64 (prmOf s).T, (prmOf s).tl⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  obtain S₆ : SavedAt s₆.mem (prmOf s).W s := F.saved.frame f₆ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (L.t_w' (d := 128) (k := 16) (by decide)).symm
  obtain hret : s₆.mem.readW (w64 (s.gpr .esp)) 32 = s.mem.readW (w64 (s.gpr .esp)) 32 := by
    rw [f₆.readW (r := ⟨w64 (prmOf s).SP, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.retT) (by decide)]
    exact F.frame.readW (r := ⟨w64 (prmOf s).SP, 4⟩) (Region.contains_self _ _) (ret_front L) (by decide)
  -- `restore`.
  refine WP.mono (exit_ok (s₀ := s) (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), F.env.ebp])
    (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), F.env.esp]; rfl)
    (by rw [rd₆, wr₆]; exact covers_left F.env.perm.w) L.ww S₆ hret) fun s₇ ⟨ab, m₇, _, _, _⟩ => ⟨ab, ?_⟩
  obtain hd : bytesAt s₆.mem (w64 (prmOf s).D) (prmOf s).n = bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n :=
    Proof.AesGcm.X86.bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.t_d.symm) (by have := L.dw; omega_using [this])
  obtain ht : bytesAt s₆.mem (w64 (prmOf s).T) (prmOf s).tl = bytesAt s₅.mem (w64 (prmOf s).W) (prmOf s).tl := by
    have := bytesAt_writeBytes_self s₅.mem (w64 (prmOf s).T) (bytesAt s₅.mem (w64 (prmOf s).W) (prmOf s).tl)
      (by rw [length_bytesAt]; have := L.tl16; omega_using [this])
    rw [length_bytesAt] at this
    rw [m₆]; exact this
  show _ = (bytesAt s₇.mem (w64 (prmOf s).D) (prmOf s).n, bytesAt s₇.mem (w64 (prmOf s).T) (prmOf s).tl)
  rw [m₇, hd, ht]
  exact out

/-- `ok` into `eax`. -/
theorem retEax_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) :
    ∃ s', runBlock isa [.mov .eax (slot okO)] s = some s' ∧ s'.gpr .eax = slotv s.mem p.W okO ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, by grun [E.ebp, L.aW, E.perm.wR], by gregs [], fun r h₁ => by gregs [h₁], by gmems [], by gmems [],
    by gmems []⟩

/-- `vg_aes_ocb_open`. -/
theorem open_wp (v : BlocksImpl) {s : State} (h : openPre s) :
    WP isa («open» (callees v)) s fun s' => abiPreserved s s' ∧ openX86.post s s' := by
  obtain h₁ := onePre_open h
  obtain L := lay_of h₁
  unfold «open»
  refine WP.seq (WP.mono (openFront_ok v h₁ (bytesAt s.mem (w64 (prmOf s).T) (prmOf s).tl)) fun s₅ ⟨F, out⟩ => ?_)
  let p := prmOf s
  try rewrite [show prmOf s = p from rfl] at *
  have hp : p = prmOf s := rfl
  have ht := L.tl16
  -- The received tag.
  refine WP.seq (WP.mono (recv_ok L F.env) fun s₆ ⟨m₆, g₆, rd₆, wr₆⟩ => ?_)
  obtain f₆ : Frame [⟨w64 p.W, p.tl⟩] s₅.mem s₆.mem := by rw [m₆]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  obtain F₆ : Frame (mutR p) s₅.mem s₆.mem := frame_toMut f₆ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨wA p.W, by simp, Region.sub_prefix (by omega_using [ht])⟩
  obtain E₆ : Env p s₆ := F.env.mut L (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), F.env.ebp])
    (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), F.env.esp]) rd₆ wr₆ F₆
  -- The comparison.
  refine WP.seq (WP.mono (cmp_ok L E₆) fun s₇ ⟨m₇, g₇, rd₇, wr₇⟩ => ?_)
  obtain f₇ : Frame [⟨w64 p.W + BitVec.ofNat 64 okO, 4⟩] s₆.mem s₇.mem := by
    rw [m₇]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain F₇ : Frame (mutR p) s₆.mem s₇.mem := frame_toMut f₇ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  obtain E₇ : Env p s₇ := E₆.mut L
    (by rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), E₆.ebp])
    (by rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), E₆.esp]) rd₇ wr₇ F₇
  obtain hok : slotv s₇.mem p.W okO = if decide (bytesAt s₆.mem (w64 p.W) p.tl =
      bytesAt s₆.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl) then BitVec.ofNat 32 1 else BitVec.ofNat 32 0 := by
    rw [slotv_eq, m₇, Mem.readW_writeW_self32]; simp only [decide_eq_true_eq]
  -- The mask.
  refine WP.seq (WP.mono (mask_ok L E₇ hok) fun s₈ ⟨m₈, g₈, rd₈, wr₈⟩ => ?_)
  obtain f₈ : Frame [⟨w64 p.D, p.n⟩] s₇.mem s₈.mem := by rw [m₈]; exact writeBytes_frame' _ (length_mask _ _ _ _)
  obtain F₈ : Frame (mutR p) s₇.mem s₈.mem := frame_toMut f₈ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact inMut_d p
  obtain E₈ : Env p s₈ := E₇.mut L (by rw [g₈ _ (by decide) (by decide) (by decide) (by decide), E₇.ebp])
    (by rw [g₈ _ (by decide) (by decide) (by decide) (by decide), E₇.esp]) rd₈ wr₈ F₈
  -- `ok` and `restore`.
  rw [WP.block_append_iff]
  obtain ⟨s₉, run₉, ax₉, g₉, m₉, rd₉, wr₉⟩ := retEax_ok L E₈
  refine WP.of_runBlock ⟨s₉, run₉, ?_⟩
  obtain fr := (F₆.trans F₇).trans F₈
  obtain hret : s₉.mem.readW (w64 (s.gpr .esp)) 32 = s.mem.readW (w64 (s.gpr .esp)) 32 := by
    rw [m₉, show s.gpr .esp = p.SP from rfl, ret_mut L fr]
    exact F.frame.readW (r := ⟨w64 p.SP, 4⟩) (Region.contains_self _ _) (ret_front L) (by decide)
  refine WP.mono (exit_ok (s₀ := s) (by rw [g₉ _ (by decide), E₈.ebp])
    (by rw [g₉ _ (by decide), E₈.esp]; rfl) (by rw [rd₉, wr₉]; exact covers_left E₈.perm.w) L.ww
    (by rw [m₉]; exact SavedAt.mut L fr F.saved) hret) fun s₁₀ ⟨ab, m₁₀, ax₁₀, _, _⟩ => ⟨ab, ?_⟩
  -- The values.
  obtain tg₆ : bytesAt s₆.mem (w64 p.W) p.tl = bytesAt s.mem (w64 p.T) p.tl := by
    have := bytesAt_writeBytes_self s₅.mem (w64 p.W) (bytesAt s₅.mem (w64 p.T) p.tl)
      (by rw [length_bytesAt]; omega_using [ht])
    rw [length_bytesAt] at this
    rw [m₆, this]
    exact bytes_front L.t_w L.bt L.t_d (by omega_using [ht]) F.frame
  obtain t2₆ : bytesAt s₆.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl = bytesAt s₅.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl :=
    Proof.AesGcm.X86.bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using Lay.w_w (W := p.W) (a := t2O) (n := p.tl) (d := 0) (k := p.tl) (.inr (by simp only [t2O]; omega_using [ht]))
        (by simp only [t2O]; omega_using [ht]) (by omega_using [ht])) (by omega_using [ht])
  obtain d₇ : bytesAt s₇.mem (w64 p.D) p.n = bytesAt s₅.mem (w64 p.D) p.n := by
    rw [Proof.AesGcm.X86.bytesAt_frame f₇ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)) (by have := L.dw; omega_using [this]),
      Proof.AesGcm.X86.bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.d_w.sub_right (Region.sub_prefix (by omega_using [ht])))
        (by have := L.dw; omega_using [this])]
  obtain ok₈ : slotv s₈.mem p.W okO = slotv s₇.mem p.W okO :=
    f₈.readW (r := ⟨w64 p.W + BitVec.ofNat 64 okO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.d_w' (by decide)).symm) (by decide)
  obtain out₈ : bytesAt s₈.mem (w64 p.D) p.n = if decide (bytesAt s₆.mem (w64 p.W) p.tl =
      bytesAt s₆.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl) then bytesAt s₇.mem (w64 p.D) p.n else zeros p.n := by
    obtain hlm := length_mask s₇.mem (w64 p.D) (decide (bytesAt s₆.mem (w64 p.W) p.tl =
      bytesAt s₆.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl)) p.n
    have := bytesAt_writeBytes_self s₇.mem (w64 p.D) _ (by rw [hlm]; have := L.dw; omega_using [this])
    rw [hlm] at this
    rw [m₈]; exact this
  obtain eax : s₁₀.gpr .eax = if decide (bytesAt s₆.mem (w64 p.W) p.tl =
      bytesAt s₆.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl) then BitVec.ofNat 32 1 else BitVec.ofNat 32 0 := by
    rw [ax₁₀, ax₉, ok₈, hok]
  rw [tg₆, t2₆, d₇] at out₈
  rw [tg₆, t2₆] at eax
  obtain mem : bytesAt s₁₀.mem (w64 p.D) p.n = bytesAt s₈.mem (w64 p.D) p.n := by rw [m₁₀, m₉]
  show openPost (openResult s) s₁₀ (w64 p.D) p.n
  by_cases hc : bytesAt s₅.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl = bytesAt s.mem (w64 p.T) p.tl
  · have hc' : bytesAt s.mem (w64 p.T) p.tl = bytesAt s₅.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl := hc.symm
    obtain r : openResult s = some (bytesAt s₅.mem (w64 p.D) p.n) := out.trans (by simp only [hc, ↓reduceIte])
    obtain a : s₁₀.gpr .eax = 1 := by rw [eax]; simp only [hc', decide_true, ↓reduceIte]; rfl
    obtain d : bytesAt s₁₀.mem (w64 p.D) p.n = bytesAt s₅.mem (w64 p.D) p.n := by
      rw [mem, out₈]; simp only [hc', decide_true, ↓reduceIte]
    exact openPost_some r a d
  · have hc' : ¬ bytesAt s.mem (w64 p.T) p.tl = bytesAt s₅.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl :=
      fun e => hc e.symm
    obtain r : openResult s = none := out.trans (by simp only [hc, ↓reduceIte])
    obtain a : s₁₀.gpr .eax = 0 := by rw [eax]; simp only [hc', decide_false, Bool.false_eq_true, ↓reduceIte]; rfl
    obtain d : bytesAt s₁₀.mem (w64 p.D) p.n = zeros p.n := by
      rw [mem, out₈]; simp only [hc', decide_false, Bool.false_eq_true, ↓reduceIte]
    exact openPost_none r a d

end VG.Proof.AesOcb.X86

end

end


/-!
# AES-OCB on x86: `Verified`

Untrusted: everything here is checked by Lean. Correctness (`seal_wp`,
`open_wp`, `init_correct`) and constant time (`seal_ct`, `open_ct`,
`init_ct`) for any implementations `v` of `vg_aes_encrypt_blocks`,
`vg_aes_decrypt_blocks` and `vg_aes_expand_key_scratch`, a state satisfying each
precondition, and the shared contracts with the working space as a last
argument (`Proof/AesOcb/Scratch.lean`), with 24 bytes of stack: the
arguments and return address of the calls, whose callees use no stack.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.Impl.AesOcb.X86
open VG.Proof.Aes.X86 (BlocksImpl)

theorem seal_correct (v : BlocksImpl) (s : State) (hs : sealX86.pre s) :
    ∃ t s', Exec isa («seal» (callees v)) s t s' ∧ abiPreserved s s' ∧ sealX86.post s s' :=
  seal_wp v hs

theorem open_correct (v : BlocksImpl) (s : State) (hs : openX86.pre s) :
    ∃ t s', Exec isa («open» (callees v)) s t s' ∧ abiPreserved s s' ∧ openX86.post s s' :=
  open_wp v hs

/-- A state satisfying the precondition of `vg_aes_ocb_seal`: the key
context at `0x1000`, 10 rounds, a 7-byte nonce at `0x2000`, no associated
data (at `0x2100`), no data (at `0x3000`), a 4-byte tag at `0x4000` and
`work` at `0x5000`, as stack arguments at `0x8004`. -/
def sealSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x20
    else if a = 0x8010 then 7 else if a = 0x8015 then 0x21 else if a = 0x801d then 0x30
    else if a = 0x8025 then 0x40 else if a = 0x8028 then 4 else if a = 0x802d then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 4⟩, ⟨0x5000, 2560⟩, ⟨0x8004, 44⟩]

/-- As `sealSat`, with the tag read only. -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x4000, 4⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x5000, 2560⟩, ⟨0x8004, 44⟩] }

theorem sealSat_args : arg sealSat 0 = 0x1000 ∧ arg sealSat 1 = 10 ∧ arg sealSat 2 = 0x2000 ∧ arg sealSat 3 = 7 ∧
    arg sealSat 4 = 0x2100 ∧ arg sealSat 5 = 0 ∧ arg sealSat 6 = 0x3000 ∧ arg sealSat 7 = 0 ∧
    arg sealSat 8 = 0x4000 ∧ arg sealSat 9 = 4 ∧ arg sealSat 10 = 0x5000 ∧ argAddr sealSat 0 = 0x8004 := by
  decide

theorem openSat_args : arg openSat 0 = 0x1000 ∧ arg openSat 1 = 10 ∧ arg openSat 2 = 0x2000 ∧ arg openSat 3 = 7 ∧
    arg openSat 4 = 0x2100 ∧ arg openSat 5 = 0 ∧ arg openSat 6 = 0x3000 ∧ arg openSat 7 = 0 ∧
    arg openSat 8 = 0x4000 ∧ arg openSat 9 = 4 ∧ arg openSat 10 = 0x5000 ∧ argAddr openSat 0 = 0x8004 :=
  sealSat_args

theorem seal_verified (v : BlocksImpl) :
    Verified X86.target («seal» (callees v)) (Proof.AesOcb.sealScratchContract X86.abi 24) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e⟩ := sealSat_args
    have esp : sealSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Proof.AesOcb.sealRoundsPost, sealX86, sealPre, oneLay, onePub, ctxR, nonceR, aadR, dataR, tagR, workR, argsR', retR,
      stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e, esp] using sealSat)

theorem open_verified (v : BlocksImpl) :
    Verified X86.target («open» (callees v)) (Proof.AesOcb.openScratchContract X86.abi 24) :=
  Verified.of_correct (open_correct v) (open_ct v) (by
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e⟩ := openSat_args
    have esp : openSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
      Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openX86, openPost, openResult, openPre, oneLay, onePub, ctxR, nonceR,
      aadR, dataR, tagR, workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e, esp] using openSat)

/-- A state satisfying `vg_aes_ocb_init`'s precondition: a key of 16 bytes
at `0x1000`, the context at `0x2000` and the scratch buffer at `0x4000`, as
stack arguments at `0x8004`. -/
def initSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 16 else if a = 0x800d then 0x20
    else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 16⟩]

theorem init_verified (v : BlocksImpl) :
    Verified X86.target (init (callees v)) (Proof.AesOcb.initScratchContract X86.abi 24) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    obtain a0 : arg initSat 0 = 0x1000 := by decide
    obtain a1 : arg initSat 1 = 16 := by decide
    obtain a2 : arg initSat 2 = 0x2000 := by decide
    obtain a3 : arg initSat 3 = 0x4000 := by decide
    obtain e : argAddr initSat 0 = 0x8004 := by decide
    have esp : initSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesOcb.initScratchContract, Proof.AesOcb.initScratchSig, Spec.Ocb.initPre,
      Spec.Ocb.initPost, initX86, initPre, keyR, ictxR, scrR, iargsR, retR, stackR, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes] [a0, a1, a2, a3, e, esp] using initSat)

end VG.Proof.AesOcb.X86

end

end


/-!
# AES-OCB on x86, with its working space on the stack

Every function runs its code, proved with the working space as its last
argument (`Verified.lean`), in a frame that allocates it and copies the
arguments passed on the stack (`Verified.stackScratch`): the return address,
the argument slots (ten for `seal` and `open`, three for `init`) and the 2560
bytes of working space, 2608 and 2580 bytes. The code's own calls use 24
bytes below it. The copies are read only where the pre- and postconditions
read the buffers, and `open`'s leak, whether it succeeds, reads only its
buffers (`Proof/AesOcb/Scratch.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.Impl.AesOcb.X86
open VG.Proof.Aes.X86 (BlocksImpl)

theorem noEsp_of {c : Prog isa} (h : NoSp c) :
    c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [h i hi]

variable (v : BlocksImpl)

theorem seal_noEsp : («seal» (callees v)).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [«seal», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, wholeIn, pass, quad, single, lAddr, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, tagOut, callBlocks, blocksFrame, callees, Code.allInstrs,
    noEsp_of v.encNosp, noEsp_of v.decNosp, ↓reduceIte]
  decide +kernel

theorem open_noEsp : («open» (callees v)).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [«open», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, wholeIn, pass, quad, single, lAddr, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, recv, cmp, mask, callBlocks, blocksFrame, callees, Code.allInstrs,
    noEsp_of v.encNosp, noEsp_of v.decNosp, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem init_noEsp : (init (callees v)).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [init, Impl.AesGcm.X86.entry, keyFrame, blocksFrame, callees, Code.allInstrs, noEsp_of v.encNosp,
    noEsp_of v.expandNosp]
  decide +kernel

theorem seal_stackUse : stackUse («seal» (callees v)) ≤ 24 := by
  simp only [«seal», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, wholeIn, pass, quad, single, lAddr, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, tagOut, callBlocks, blocksFrame, callees, stackUse, v.encStack,
    v.decStack, ↓reduceIte]
  decide +kernel

theorem open_stackUse : stackUse («open» (callees v)) ≤ 24 := by
  simp only [«open», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, wholeIn, pass, quad, single, lAddr, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, recv, cmp, mask, callBlocks, blocksFrame, callees, stackUse,
    v.encStack, v.decStack, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem init_stackUse : stackUse (init (callees v)) ≤ 24 := by
  simp only [init, Impl.AesGcm.X86.entry, keyFrame, blocksFrame, callees, stackUse, v.encStack, v.expandStack]
  decide +kernel

theorem seal_spSafe : («seal» (callees v)).all (fun i => !isa.writesSp i) = true := by
  simp only [«seal», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, wholeIn, pass, quad, single, lAddr, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, tagOut, callBlocks, blocksFrame, callees, Code.all, v.encSpSafe,
    v.decSpSafe, Bool.and_true, ↓reduceIte]
  decide +kernel

theorem open_spSafe : («open» (callees v)).all (fun i => !isa.writesSp i) = true := by
  simp only [«open», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, wholeIn, pass, quad, single, lAddr, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, recv, cmp, mask, callBlocks, blocksFrame, callees, Code.all,
    v.encSpSafe, v.decSpSafe, Bool.false_eq_true, Bool.and_true, ↓reduceIte]
  decide +kernel

theorem init_spSafe : (init (callees v)).all (fun i => !isa.writesSp i) = true := by
  simp only [init, Impl.AesGcm.X86.entry, keyFrame, blocksFrame, callees, Code.all, v.encSpSafe, v.expandSpSafe,
    Bool.and_true]
  decide +kernel

/-- A state satisfying `vg_aes_ocb_seal`'s precondition, without the working
space: as `sealSat`, with ten stack arguments. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x4000, 4⟩, ⟨0x8004, 40⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesOcb.sealRoundsContract X86.abi 2632).pre s := by
  implies_sat [Proof.AesOcb.sealRoundsContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Proof.AesOcb.sealRoundsPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [sealFrameSat, sealSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using sealFrameSat

/-- A state satisfying `vg_aes_ocb_open`'s precondition, without the working
space: as `sealFrameSat`, with the tag read only. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x4000, 4⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x8004, 40⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesOcb.openRoundsContract X86.abi 2632).pre s := by
  implies_sat [Proof.AesOcb.openRoundsContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Proof.AesOcb.openRoundsPost,
    Spec.Ocb.openLeak, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [openFrameSat, sealSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using openFrameSat

/-- A state satisfying `vg_aes_ocb_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩, ⟨0x8004, 12⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Ocb.initContract X86.abi 2604).pre s := by
  implies_sat [Spec.Ocb.initContract, Spec.Ocb.initSig, Spec.Ocb.initPre, Spec.Ocb.initPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using initFrameSat

theorem seal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2608 10 («seal» (callees v)))
      (Proof.AesOcb.sealRoundsContract X86.abi 2632) :=
  X86.Verified.stackScratch (sig := Spec.Ocb.sealSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ocb.sealPre X86.abi.ptrBits) (post := Proof.AesOcb.sealRoundsPost X86.abi.ptrBits)
    (wa := true) (stack := 24) (bytes := 2608) (seal_verified v) (by decide) (seal_noEsp v)
    (seal_stackUse v) (sealPre_local _) (sealPost_local _) (sealPostOut_local _) sealFrameSat_pre

theorem open_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2608 10 («open» (callees v)))
      (Proof.AesOcb.openRoundsContract X86.abi 2632) :=
  X86.Verified.stackScratch (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ocb.openPre X86.abi.ptrBits) (post := Proof.AesOcb.openRoundsPost X86.abi.ptrBits)
    (wa := true) (stack := 24) (leak := some (Spec.Ocb.openLeak X86.abi.ptrBits)) (bytes := 2608)
    (open_verified v) (by decide) (open_noEsp v) (open_stackUse v) (openPre_local _) (openPost_local _) (openPostOut_local _)
    openFrameSat_pre (hleak := openLeak_local _)

theorem init_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2580 3 (init (callees v)))
      (Spec.Ocb.initContract X86.abi 2604) :=
  X86.Verified.stackScratch (sig := Spec.Ocb.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Ocb.initPre X86.abi.ptrBits) (post := Spec.Ocb.initPost X86.abi.ptrBits)
    (wa := true) (stack := 24) (bytes := 2580) (init_verified v) (by decide) (init_noEsp v)
    (init_stackUse v) (initPre_local _) (initPost_local _) (initPostOut_local _) initFrameSat_pre

end VG.Proof.AesOcb.X86
