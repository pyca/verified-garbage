import VerifiedGarbage.Proof.AesGcmSiv.X86.Open
import VerifiedGarbage.Proof.AesGcmSiv.X86.CryptCT

/-!
# AES-GCM-SIV on x86: `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` are constant time

Untrusted: everything here is checked by Lean. The arguments and `esp` are
public, and so is everything the pieces' preconditions say (`prmOf`). The
entry loads `work` from the stack, at `esp`, and saves our caller's registers
and the arguments through it (`entry_ct`); `cmp` computes the result without
a branch, and `mask` loops over the data's length alone (`mask_ct`); the
other pieces are constant time from `Env` (`keys_ct`, `polyval_ct`,
`tag_ct`, `crypt_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.X86 (at_ imm slot argOp)
open VG.Proof.AesGcm.X86 (CT w64 GcmImpl argA argA_contains)

/-- The public arguments are a function of what `onePub` says is public. -/
theorem prmOf_pub {s₁ s₂ : State} (h : onePub s₁ s₂) : prmOf s₁ = prmOf s₂ := by
  obtain ⟨h₁, h₂⟩ := h
  simp only [prmOf, h₁, h₂ 0 (by decide), h₂ 1 (by decide), h₂ 2 (by decide), h₂ 3 (by decide), h₂ 4 (by decide),
    h₂ 5 (by decide), h₂ 6 (by decide), h₂ 7 (by decide), h₂ 8 (by decide)]

theorem entryLoad_ok {p : Prm} {s : State} (h : onePre s) (hp : prmOf s = p) :
    ∃ s', runBlock isa [.mov .eax (argOp 8)] s = some s' ∧ s'.gpr .eax = p.W ∧ s'.gpr .esp = p.SP := by
  have Ao := argsOk_of h
  have hw : p.W = arg s 8 := hp ▸ rfl
  have hsp : p.SP = s.gpr .esp := hp ▸ rfl
  have rA := Ao.rA
  have fa := Ao.fa
  generalize hSP : s.gpr .esp = SP at rA fa hsp
  have i₀ : InRegions (s.rd ++ s.wr) (argA SP 8) 4 :=
    rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa⟩
  refine ⟨_, by grun [hSP, i₀], ?_, ?_⟩
  · rw [gpr_setReg_self, hw, ← hSP]; rfl
  · rw [gpr_setReg_of_ne _ _ (by decide), hSP, hsp]

theorem entrySave_ct {p : Prm} :
    CT (fun s => s.gpr .eax = p.W ∧ s.gpr .esp = p.SP)
      (.block (Impl.AesGcm.X86.saveAt ++ entryPs.flatMap (fun q => Impl.AesGcm.X86.keep q.1 q.2))) :=
  CT.taint [.eax, .esp] (pin2 fun _ h => h) (by taint_decide)

theorem entry_ct {p : Prm} : CT (fun s => onePre s ∧ prmOf s = p) sivEntry := by
  have e : ∀ s, prmOf s = p → s.gpr .esp = p.SP := fun s h => h ▸ rfl
  rw [sivEntry_eq]
  refine CT.seq (J := fun s => s.gpr .eax = p.W ∧ s.gpr .esp = p.SP)
    (CT.taint [.esp] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [e _ h₁.2, e _ h₂.2]) (by taint_decide))
    (fun s ⟨h, hp⟩ => let ⟨s', run, ax, sp⟩ := entryLoad_ok h hp; WP.of_runBlock ⟨s', run, ax, sp⟩) entrySave_ct

/-! ## The mask -/

theorem mask_ct {p : Prm} (L : Lay p) : CT (Env p) mask := by
  refine CT.block_seq (F := fun _ s₁ => s₁.zf = some (decide (p.n = 0)) ∧ Env p s₁ ∧
      s₁.gpr .ecx = BitVec.ofNat 32 p.n) [.ebp] (pin_ebp fun s h => h.ebp) (by taint_decide)
    (fun s E => let ⟨s₁, run, _, _, cx, zf, _, E₁, _⟩ := maskTest_ok L E; ⟨s₁, run, zf, E₁, cx⟩) ?_
  refine CT.ite (decide (p.n = 0)) (fun _ ⟨_, _, zf, _⟩ => eval_e zf) (fun _ => CT.nil) fun _ => ?_
  refine CT.block_seq (F := fun _ s₂ => s₂.gpr .edi = p.D ∧ s₂.gpr .ecx = BitVec.ofNat 32 p.n) [.ebp]
    (pin_ebp fun _ ⟨_, _, _, E, _⟩ => E.ebp) (by taint_decide)
    (fun s₁ ⟨_, _, _, E₁, cx⟩ => let ⟨s₂, run, _, di, g, _⟩ := maskArgs_ok L E₁;
      ⟨s₂, run, di, by rw [g _ (by decide), cx]⟩) ?_
  exact CT.taint [.edi, .ecx] (pin2 fun _ ⟨_, _, di, cx⟩ => ⟨di, cx⟩) (by taint_decide)

/-! ## `seal` -/

theorem seal_top_ct (v : GcmImpl) {p : Prm} (L : Lay p) :
    CT (fun s => sealPre s ∧ prmOf s = p) («seal» v.callees) := by
  have tw : ∀ s, sealPre s → prmOf s = p → Covers [⟨w64 p.T, 16⟩] s.wr := fun s h hp => by
    subst hp; exact covers_of_mem (by rw [h.2.1]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  refine CT.seq (J := fun s₁ => ∃ s, (sealPre s ∧ prmOf s = p) ∧ Entered s p s₁)
    (entry_ct.mono fun s h => ⟨onePre_seal h.1, h.2⟩)
    (fun s ⟨h, hp⟩ => WP.mono (entry_ok (onePre_seal h)) fun s₁ En => ⟨s, ⟨h, hp⟩, hp ▸ En⟩) ?_
  refine CT.seq (J := fun s => ∃ σ, KeysPost p σ s ∧ Covers [⟨w64 p.T, 16⟩] σ.wr)
    ((keys_ct v L).mono fun _ ⟨_, _, En⟩ => En.env)
    (fun _ ⟨s, ⟨h, hp⟩, En⟩ => WP.mono (keys_ok v L En.env) fun _ Ky => ⟨_, Ky, by rw [En.wr]; exact tw s h hp⟩) ?_
  refine CT.seq (J := fun s => Env p s ∧ Covers [⟨w64 p.T, 16⟩] s.wr) ((polyval_ct v L).mono fun _ ⟨_, Ky, _⟩ => Ky.env)
    (fun _ ⟨_, Ky, t⟩ => WP.mono (polyval_ok v L Ky.env Ky.hkey Ky.acc) fun _ Po =>
      ⟨Po.env, by rw [Po.wr, Ky.wr]; exact t⟩) ?_
  refine CT.seq (J := fun s => Env p s ∧ Covers [⟨w64 p.T, 16⟩] s.wr)
    ((tag_ct v L (o := 0) (by decide)).mono fun _ h => h.1)
    (fun _ ⟨E, t⟩ => WP.mono (tag_ok v L E (o := 0) (by decide)) fun _ Tg => ⟨Tg.env, by rw [Tg.wr]; exact t⟩) ?_
  refine CT.seq (J := fun s => Env p s ∧ Covers [⟨w64 p.T, 16⟩] s.wr) ((crypt_ct v L).mono fun _ h => h.1)
    (fun _ ⟨E, t⟩ => WP.mono (crypt_ok v L E) fun _ Cr => ⟨Cr.env, by rw [Cr.wr]; exact t⟩) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = p.W) ((tagOut_ct L).mono fun _ h => h.1)
    (fun _ ⟨E, t⟩ => WP.mono (tagOut_ok L E t) fun _ ⟨_, _, bp, _⟩ => bp) ?_
  exact CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)

theorem seal_ct (v : GcmImpl) : ConstantTime isa sealX86.pre sealX86.pub («seal» v.callees) :=
  CT.constantTime prmOf (fun _ _ _ _ h => prmOf_pub h) fun p => by
    by_cases hex : ∃ s, sealPre s ∧ prmOf s = p
    · obtain ⟨z, hz, rfl⟩ := hex
      exact seal_top_ct v (lay_of (onePre_seal hz))
    · intro s₁ _ _ _ _ _ h
      exact (hex ⟨s₁, h.1⟩).elim

/-! ## `open` -/

theorem open_top_ct (v : GcmImpl) {p : Prm} (L : Lay p) :
    CT (fun s => openPre s ∧ prmOf s = p) («open» v.callees) := by
  refine CT.seq (J := fun s₁ => ∃ s, (openPre s ∧ prmOf s = p) ∧ Entered s p s₁)
    (entry_ct.mono fun s h => ⟨onePre_open h.1, h.2⟩)
    (fun s ⟨h, hp⟩ => WP.mono (entry_ok (onePre_open h)) fun s₁ En => ⟨s, ⟨h, hp⟩, hp ▸ En⟩) ?_
  refine CT.seq (J := Env p) ((recvTag_ct L).mono fun _ ⟨_, _, En⟩ => En.env)
    (fun _ ⟨_, _, En⟩ => WP.mono (recvTag_ok L En.env) fun _ h => h.1) ?_
  refine CT.seq (J := fun s => ∃ σ, KeysPost p σ s) (keys_ct v L)
    (fun _ E => WP.mono (keys_ok v L E) fun s Ky => ⟨_, Ky⟩) ?_
  refine CT.seq (J := fun s => Env p s ∧
      Spec.Gcm.blockAt s.mem (w64 p.W + BitVec.ofNat 64 64) =
        GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt s.mem (w64 p.W + BitVec.ofNat 64 16) 16)) ∧
      Spec.Gcm.blockAt s.mem (w64 p.W + BitVec.ofNat 64 80) = 0)
    ((crypt_ct v L).mono fun _ ⟨_, Ky⟩ => Ky.env)
    (fun _ ⟨_, Ky⟩ => WP.mono (crypt_ok v L Ky.env) fun _ Cr => ⟨Cr.env, (keys_crypt L Ky Cr).1, (keys_crypt L Ky Cr).2.1⟩) ?_
  refine CT.seq (J := Env p) ((polyval_ct v L).mono fun _ h => h.1)
    (fun _ h => WP.mono (polyval_ok v L h.1 h.2.1 h.2.2) fun _ Po => Po.env) ?_
  refine CT.seq (J := Env p) (tag_ct v L (o := 240) (by decide))
    (fun _ E => WP.mono (tag_ok v L E (o := 240) (by decide)) fun _ Tg => Tg.env) ?_
  refine CT.seq (J := fun s => Env p s ∧ ∃ c : Bool, s.gpr .eax = BitVec.ofNat 32 (if c then 1 else 0))
    (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun s E => ?_) ?_
  · obtain ⟨s₆, run₆, ax₆, hm₆, bp₆, sp₆, rd₆, wr₆⟩ := cmp_ok L E
    refine WP.of_runBlock ⟨s₆, run₆, E.keep (by rw [bp₆, E.ebp]) (by rw [sp₆, E.esp]) rd₆ wr₆ hm₆,
      decide (bytesAt s.mem (w64 p.W) 16 = bytesAt s.mem (w64 p.W + BitVec.ofNat 64 240) 16), ?_⟩
    rw [ax₆]; simp only [okVal, decide_eq_true_eq]
  refine CT.seq (J := Env p) ((mask_ct L).mono fun _ h => h.1)
    (fun _ ⟨E, _, hc⟩ => WP.mono (mask_ok L E hc) fun _ Mk => Mk.env) ?_
  exact CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide)

theorem open_ct (v : GcmImpl) : ConstantTime isa openX86.pre openX86.pub («open» v.callees) :=
  CT.constantTime prmOf (fun _ _ _ _ h => prmOf_pub h) fun p => by
    by_cases hex : ∃ s, openPre s ∧ prmOf s = p
    · obtain ⟨z, hz, rfl⟩ := hex
      exact open_top_ct v (lay_of (onePre_open hz))
    · intro s₁ _ _ _ _ _ h
      exact (hex ⟨s₁, h.1⟩).elim

end VG.Proof.AesGcmSiv.X86
