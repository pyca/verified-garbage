module

public import VerifiedGarbage.Proof.AesOcb.Rounds
import VerifiedGarbage.Proof.AesOcb.X86.SealCT
import VerifiedGarbage.Proof.AesOcb.X86.Init
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesOcb.Scratch
public import VerifiedGarbage.Proof.AesOcb.X86.Callee
public import VerifiedGarbage.Proof.AesOcb.X86.Contract
public import VerifiedGarbage.Proof.AesOcb.X86.Front
import VerifiedGarbage.Proof.AesOcb.X86.TagIO
import VerifiedGarbage.Proof.AesOcb.X86.Run
import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.AesGcm.X86.Absorb
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Spec.Ocb.Contract
public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Aes.X86.Keys

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
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, tagOut, callBlocks, blocksFrame, callees, Code.allInstrs,
    noEsp_of v.encNosp, noEsp_of v.decNosp, ↓reduceIte]
  decide +kernel

theorem open_noEsp : («open» (callees v)).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [«open», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, recv, cmp, mask, callBlocks, blocksFrame, callees, Code.allInstrs,
    noEsp_of v.encNosp, noEsp_of v.decNosp, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem init_noEsp : (init (callees v)).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [init, Impl.AesGcm.X86.entry, keyFrame, blocksFrame, callees, Code.allInstrs, noEsp_of v.encNosp,
    noEsp_of v.expandNosp]
  decide +kernel

theorem seal_stackUse : stackUse («seal» (callees v)) ≤ 24 := by
  simp only [«seal», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, tagOut, callBlocks, blocksFrame, callees, stackUse, v.encStack,
    v.decStack, ↓reduceIte]
  decide +kernel

theorem open_stackUse : stackUse («open» (callees v)) ≤ 24 := by
  simp only [«open», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, recv, cmp, mask, callBlocks, blocksFrame, callees, stackUse,
    v.encStack, v.decStack, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem init_stackUse : stackUse (init (callees v)) ≤ 24 := by
  simp only [init, Impl.AesGcm.X86.entry, keyFrame, blocksFrame, callees, stackUse, v.encStack, v.expandStack]
  decide +kernel

theorem seal_spSafe : («seal» (callees v)).all (fun i => !isa.writesSp i) = true := by
  simp only [«seal», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, tagOut, callBlocks, blocksFrame, callees, Code.all, v.encSpSafe,
    v.decSpSafe, Bool.and_true, ↓reduceIte]
  decide +kernel

theorem open_spSafe : («open» (callees v)).all (fun i => !isa.writesSp i) = true := by
  simp only [«open», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest,
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
    (seal_stackUse v) (sealPre_local _) (sealPost_local _) sealFrameSat_pre

theorem open_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2608 10 («open» (callees v)))
      (Proof.AesOcb.openRoundsContract X86.abi 2632) :=
  X86.Verified.stackScratch (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ocb.openPre X86.abi.ptrBits) (post := Proof.AesOcb.openRoundsPost X86.abi.ptrBits)
    (wa := true) (stack := 24) (leak := some (Spec.Ocb.openLeak X86.abi.ptrBits)) (bytes := 2608)
    (open_verified v) (by decide) (open_noEsp v) (open_stackUse v) (openPre_local _) (openPost_local _)
    openFrameSat_pre (hleak := openLeak_local _)

theorem init_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2580 3 (init (callees v)))
      (Spec.Ocb.initContract X86.abi 2604) :=
  X86.Verified.stackScratch (sig := Spec.Ocb.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Ocb.initPre X86.abi.ptrBits) (post := Spec.Ocb.initPost X86.abi.ptrBits)
    (wa := true) (stack := 24) (bytes := 2580) (init_verified v) (by decide) (init_noEsp v)
    (init_stackUse v) (initPre_local _) (initPost_local _) initFrameSat_pre

end VG.Proof.AesOcb.X86
