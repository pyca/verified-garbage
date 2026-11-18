module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Body
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contract
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.AesGcm.AArch64.Open
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Open
import VerifiedGarbage.Proof.AesGcm.AArch64.BodyCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.BodyCT
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamInit
meta import VerifiedGarbage.Proof.AesGcm.AArch64.StreamInit
import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
meta import VerifiedGarbage.Proof.AesGcm.AArch64.StreamFinish
meta import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Body
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Contract

/-! ### `AesGcm.AArch64.StreamCrypt`, which this module and modules that import it used -/

section

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers and sets up the body's arguments (`crEntry_ok`); the body
encrypts (`encBody_ok`) or decrypts (`decBody_ok`) and absorbs the
ciphertext, for any message so far of those lengths (`WP.forall_det`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghashInput StreamRepr gctr inc32)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- After the entry: the body's arguments. -/
theorem crEntry_ok {s : State} {Ctx St D W : Addr} {n : Nat} (hCtx : s.gpr .x0 = Ctx) (hSt : s.gpr .x2 = St)
    (hD : s.gpr .x5 = D) (hn : (s.gpr .x6).toNat = n) (hW : s.gpr .x7 = W) (hperm : Perm Ctx St W s) :
    WP isa (.block crEntry) s fun s' => Env Ctx St W s.sp s' ∧ Kept s'.gpr s' ∧
      s'.gpr .x22 = BitVec.ofNat 64 (s.gpr .x1).toNat ∧
      s'.gpr .x25 = BitVec.ofNat 64 ((s.gpr .x3).toNat % 16) ∧ s'.gpr .x26 = BitVec.ofNat 64 n ∧
      s'.gpr .x27 = BitVec.ofNat 64 (s.gpr .x4).toNat ∧ s'.gpr .x28 = D ∧ s'.mem = savedMem s.mem W s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s .x7 hW hperm.w
  have hn' : s.gpr .x6 = BitVec.ofNat 64 n := by rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨s₂, run₂, x19₂, x20₂, x21₂, x22₂, x26₂, x27₂, x28₂, x25₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x7, mov .x20 .x2, mov .x21 .x0, mov .x22 .x1, mov .x26 .x6, mov .x27 .x4, mov .x28 .x5,
        imm .x9 15, .logic .and .x .x25 .x3 .x9] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x20 = St ∧ s₂.gpr .x21 = Ctx ∧
      s₂.gpr .x22 = BitVec.ofNat 64 (s.gpr .x1).toNat ∧ s₂.gpr .x26 = BitVec.ofNat 64 n ∧
      s₂.gpr .x27 = BitVec.ofNat 64 (s.gpr .x4).toNat ∧ s₂.gpr .x28 = D ∧
      s₂.gpr .x25 = BitVec.ofNat 64 ((s.gpr .x3).toNat % 16) ∧
      s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, g₁, hW]
    · simp [gpr_write, g₁, hSt]
    · simp [gpr_write, g₁, hCtx]
    · simp [gpr_write, g₁]
    · simp [gpr_write, g₁, hn']
    · simp [gpr_write, g₁]
    · simp [gpr_write, g₁, hD]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, g₁, BitVec.setWidth_eq]
      rw [show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  exact ⟨⟨x19₂, x20₂, x21₂, by rw [sp₂, sp₁], hperm.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])⟩,
    fun _ _ => rfl, x22₂, x25₂, x26₂, x27₂, x28₂, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- What a run of `encrypt` or `decrypt` leaves, for the message `a`, `c` so far. -/
def CrRun (s : State) (a c : List Byte) (icb : Block) (e out : List Byte) (s' : State) : Prop :=
  GprAbi s s' ∧
  Frame (savedR (s.gpr .x7) :: bodyFrame (s.gpr .x2) (s.gpr .x7) (s.gpr .x5) (s.gpr .x6).toNat) s.mem s'.mem ∧
  (Absorbed s.mem (s.gpr .x2 + BitVec.ofNat 64 16) (s.gpr .x2 + BitVec.ofNat 64 32)
      (Spec.Gcm.ctxH s.mem (s.gpr .x0)) (ghashInput a c) →
    Ctr s.mem (s.gpr .x2 + BitVec.ofNat 64 48) (s.gpr .x2 + BitVec.ofNat 64 64)
      (ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat) icb (s.gpr .x4).toNat →
    Absorbed s'.mem (s.gpr .x2 + BitVec.ofNat 64 16) (s.gpr .x2 + BitVec.ofNat 64 32)
      (Spec.Gcm.ctxH s.mem (s.gpr .x0)) (ghashInput a (c ++ e)) ∧
    Ctr s'.mem (s.gpr .x2 + BitVec.ofNat 64 48) (s.gpr .x2 + BitVec.ofNat 64 64)
      (ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat) icb ((s.gpr .x4).toNat + (s.gpr .x6).toNat) ∧
    bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat = out)

/-- The entry, `body`, and the exit: what `body` does, moved to the entry
state. -/
theorem cr_run {body : Prog isa} {s : State} (hs : streamCryptPre s) {a c : List Byte}
    (ha : a.length % 16 = (s.gpr .x3).toNat % 16) (hc : c.length = (s.gpr .x4).toNat) {icb : Block}
    {E O : Mem → List Byte}
    (hE : ∀ m, Frame [savedR (s.gpr .x7)] s.mem m → E m = E s.mem)
    (hO : ∀ m, Frame [savedR (s.gpr .x7)] s.mem m → O m = O s.mem)
    (hb : ∀ {k : Reg → BitVec 64} {s₁ : State}, Lay (s.gpr .x0) (s.gpr .x2) (s.gpr .x7) →
      BodyIn (s.gpr .x0) (s.gpr .x2) (s.gpr .x7) s.sp k (s.gpr .x1).toNat (s.gpr .x6).toNat (s.gpr .x4).toNat
        (s.gpr .x5) a c (Spec.Gcm.ctxH s.mem (s.gpr .x0)) s₁ →
      WP isa body s₁ (BodyOut (s.gpr .x0) (s.gpr .x2) (s.gpr .x7) s.sp k (s.gpr .x1).toNat (s.gpr .x6).toNat
        (s.gpr .x4).toNat (s.gpr .x5) a c (Spec.Gcm.ctxH s.mem (s.gpr .x0)) icb (E s₁.mem) (O s₁.mem) s₁.mem)) :
    WP isa (.seq (.block crEntry) (.seq body (.block restore))) s (CrRun s a c icb (E s.mem) (O s.mem)) := by
  unfold CrRun
  simp only [streamCryptPre] at hs
  obtain ⟨hrd, hwr, dcs, dcd, dcw, dsd, dsw, ddw, wc, ws, wd, ww, hR⟩ := hs
  generalize hCtx : s.gpr .x0 = Ctx at *
  generalize hSt : s.gpr .x2 = St at *
  generalize hD : s.gpr .x5 = D at *
  generalize hn : (s.gpr .x6).toNat = n at *
  generalize hW : s.gpr .x7 = W at *
  generalize hRR : (s.gpr .x1).toNat = R at *
  generalize hP : (s.gpr .x4).toNat = P at *
  have L : Lay Ctx St W := Lay.of wc ws ww dcs dcw dsw
  have perm : Perm Ctx St W s :=
    ⟨covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩
  have hlt : n < 2 ^ 64 := hn ▸ (s.gpr .x6).isLt
  have hPlt : P < 2 ^ 64 := hP ▸ (s.gpr .x4).isLt
  refine WP.seq (WP.mono (crEntry_ok hCtx hSt hD hn hW perm)
    fun s₁ ⟨he₁, hk₁, x22₁, x25₁, x26₁, x27₁, x28₁, m₁, rd₁, wr₁⟩ => ?_)
  rw [hRR] at x22₁
  rw [hP] at x27₁
  have fsv : Frame [savedR W] s.mem s₁.mem := by rw [m₁]; exact savedMem_frame _ _ _
  have sW : Region.Sub (savedR W) ⟨W, 2560⟩ := Lay.wSub (by decide)
  have hH : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = Spec.Gcm.ctxH s.mem Ctx :=
    blockAt_frame fsv (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (dcw.sub_left (Lay.ctxSub (by decide))).sub_right sW)
  have hdat : DataW Ctx St W s₁ D n :=
    ⟨⟨covers_left (by rw [wr₁, hwr]; exact covers_of_mem (by simp)), hlt, wd, dsd.symm, ddw⟩,
      by rw [wr₁, hwr]; exact covers_of_mem (by simp), dcd⟩
  have hIn : BodyIn Ctx St W s.sp s₁.gpr R n P D a c (Spec.Gcm.ctxH s.mem Ctx) s₁ :=
    ⟨he₁, hk₁, x22₁, hRR ▸ hR, by rw [x25₁, ha], x26₁, x27₁, x28₁, hc, hPlt, hdat, hH⟩
  refine WP.seq (WP.mono (hb L hIn) fun s₂ h₂ => ?_)
  have hsv : SavedAt s₂.mem W s := by
    have := savedAt_save s.mem W s
    rw [← m₁] at this
    exact this.frame h₂.frame fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · rcases List.mem_append.mp hr with hr | hr
        · exact saved_tFrame L (.inr rfl) r hr
        · exact saved_crFrame L hdat r hr
      · exact saved_absFrame L (.inr rfl) r hr
  refine WP.mono (exit_ok h₂.env.x19 h₂.env.sp (covers_left h₂.env.perm.w) hsv) fun s' ⟨ga, hm, _⟩ =>
    ⟨ga, ?_, fun habs hctr => ?_⟩
  · rw [hm]
    exact (fsv.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
      (h₂.frame.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  · have hc₁ : ciphOf s₁.mem Ctx R = ciphOf s.mem Ctx R :=
      ciph_frame fsv (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dcw.sub_right sW) (hRR ▸ hR)
    have hA₁ := Absorbed.frame fsv (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact st_wpart L (by decide) ⟨by decide, by decide⟩) habs
    have hC₁ := Ctr.frame fsv (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact st_wpart L (by decide) ⟨by decide, by decide⟩) hctr
    rw [← hc₁] at hC₁
    obtain ⟨o₁, o₂, o₃⟩ := h₂.post hA₁ hC₁
    rw [hc₁] at o₂
    rw [hE _ fsv] at o₁
    rw [hO _ fsv] at o₃
    rw [hm]
    exact ⟨o₁, o₂, o₃⟩

end VG.Proof.AesGcm.AArch64

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput StreamRepr gctr inc32 ctxCiph ctxH)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- `J₀` is apart from what a run of `encrypt` or `decrypt` writes. -/
theorem st0_crRun {Ctx St W D : Addr} {n : Nat} (L : Lay Ctx St W) (hd : (⟨D, n⟩ : Region).Disjoint ⟨St, 80⟩) :
    ∀ r ∈ savedR W :: bodyFrame St W D n, (⟨St, 16⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with h | hr
  · subst h; exact st0_saved L
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact st0_disj L (by decide) (by decide)
      · exact st0_w L ⟨by decide, by decide⟩
      · exact st0_w L ⟨by decide, by decide⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hd.sub_right (Region.sub_prefix (by decide))).symm
      · exact st0_disj L (by decide) (by decide)
      · exact st0_w L ⟨by decide, by decide⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact st0_disj L (by decide) (by decide)
    · exact st0_disj L (by decide) (by decide)
    · exact st0_w L ⟨by decide, by decide⟩

/-- What does not change in the entry's writes. -/
theorem crypt_inv {s : State} (hs : streamCryptPre s) {m : Mem} (hf : Frame [savedR (s.gpr .x7)] s.mem m) :
    ciphOf m (s.gpr .x0) (s.gpr .x1).toNat = ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat ∧
      bytesAt m (s.gpr .x5) (s.gpr .x6).toNat = bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat := by
  simp only [streamCryptPre] at hs
  obtain ⟨-, -, -, -, dcw, -, -, ddw, -, -, -, -, hR⟩ := hs
  have sW : Region.Sub (savedR (s.gpr .x7)) ⟨s.gpr .x7, 2560⟩ := Lay.wSub (by decide)
  exact ⟨ciph_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dcw.sub_right sW) hR,
    bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ddw.sub_right sW) (by omega_using [])⟩

theorem lay_of_crypt {s : State} (hs : streamCryptPre s) : Lay (s.gpr .x0) (s.gpr .x2) (s.gpr .x7) ∧
    (⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region).Disjoint ⟨s.gpr .x2, 80⟩ := by
  simp only [streamCryptPre] at hs
  obtain ⟨-, -, dcs, -, dcw, dsd, dsw, -, wc, ws, -, ww, -⟩ := hs
  exact ⟨Lay.of wc ws ww dcs dcw dsw, dsd.symm⟩

theorem streamEncrypt_wp (v : GcmImpl) {s : State} (hs : streamEncryptAArch64.pre s) :
    WP isa (streamEncrypt v.callees) s fun s' => GprAbi s s' ∧ streamEncryptAArch64.post s s' := by
  have hs' : streamCryptPre s := hs
  have run : ∀ (a c : List Byte) (icb : Block), a.length % 16 = (s.gpr .x3).toNat % 16 →
      c.length = (s.gpr .x4).toNat → WP isa (streamEncrypt v.callees) s (CrRun s a c icb
        (xorKs (ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat) icb (s.gpr .x4).toNat
          (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat))
        (xorKs (ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat) icb (s.gpr .x4).toNat
          (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat))) := fun a c icb ha hc =>
    cr_run (E := fun m => xorKs (ciphOf m (s.gpr .x0) (s.gpr .x1).toNat) icb (s.gpr .x4).toNat
        (bytesAt m (s.gpr .x5) (s.gpr .x6).toNat))
      (O := fun m => xorKs (ciphOf m (s.gpr .x0) (s.gpr .x1).toNat) icb (s.gpr .x4).toNat
        (bytesAt m (s.gpr .x5) (s.gpr .x6).toNat)) hs' ha hc
      (fun m hf => by simp only [(crypt_inv hs' hf).1, (crypt_inv hs' hf).2])
      (fun m hf => by simp only [(crypt_inv hs' hf).1, (crypt_inv hs' hf).2])
      (fun L h => encBody_ok L v h icb)
  have hz : (Spec.Gcm.zeros ((s.gpr .x3).toNat % 16)).length % 16 = (s.gpr .x3).toNat % 16 := by
    rw [Proof.Gcm.length_zeros, Nat.mod_mod]
  have hz' : (Spec.Gcm.zeros (s.gpr .x4).toNat).length = (s.gpr .x4).toNat := Proof.Gcm.length_zeros _
  obtain ⟨L, hds⟩ := lay_of_crypt hs'
  let ciph := ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat
  let h := ctxH s.mem (s.gpr .x0)
  refine WP.mono (WP.forall_det (P := fun (i : List Byte × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .x2) ciph h i.1 i.2.1 (gctr ciph (inc32 (Spec.Gcm.j0 h i.1)) i.2.2) ∧
        s.gpr .x3 = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .x4).toNat = i.2.2.length)
    (Q := fun i s' =>
      StreamRepr s'.mem (s.gpr .x2) ciph h i.1 i.2.1
          (gctr ciph (inc32 (Spec.Gcm.j0 h i.1)) (i.2.2 ++ bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)) ∧
        bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat =
          (gctr ciph (inc32 (Spec.Gcm.j0 h i.1)) (i.2.2 ++ bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)).drop
            i.2.2.length)
    (run _ _ 0 hz hz') fun ⟨iv, a, p⟩ ⟨hr, hl, hp⟩ => ?_) fun s' ⟨r₀, hq⟩ =>
      ⟨r₀.1, fun iv a p hr hl hp => hq ⟨iv, a, p⟩ ⟨hr, hl, hp⟩⟩
  have hp : (s.gpr .x4).toNat = p.length := hp
  have hl : s.gpr .x3 = BitVec.ofNat 64 a.length := hl
  have ha : a.length % 16 = (s.gpr .x3).toNat % 16 := by rw [hl, toNat_mod16]
  have hlen : (gctr ciph (inc32 (Spec.Gcm.j0 h iv)) p).length = (s.gpr .x4).toNat := by
    rw [Proof.Gcm.length_gctr, hp]
  refine WP.mono (run a _ (inc32 (Spec.Gcm.j0 h iv)) ha hlen) fun s' ⟨_, hf, hpost⟩ => ?_
  obtain ⟨hj, habs, hctr⟩ := Proof.Gcm.streamRepr_iff.mp hr
  rw [hlen] at hctr
  obtain ⟨o₁, o₂, o₃⟩ := hpost habs hctr
  have he : gctr ciph (inc32 (Spec.Gcm.j0 h iv)) (p ++ bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat) =
      gctr ciph (inc32 (Spec.Gcm.j0 h iv)) p ++ xorKs (ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (inc32 (Spec.Gcm.j0 h iv)) (s.gpr .x4).toNat (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat) := by
    rw [Proof.Gcm.gctr_append, hp]; rfl
  show StreamRepr s'.mem (s.gpr .x2) ciph h iv a _ ∧ _
  rw [he]
  refine ⟨Proof.Gcm.streamRepr_iff.mpr ⟨?_, o₁, ?_⟩, ?_⟩
  · rw [← hj]; exact blockAt_frame hf (st0_crRun L hds)
  · rw [List.length_append, hlen, Proof.Gcm.length_xorKs, length_bytesAt]; exact o₂
  · rw [List.drop_left' (by rw [hlen, hp]), o₃]

theorem streamDecrypt_wp (v : GcmImpl) {s : State} (hs : streamDecryptAArch64.pre s) :
    WP isa (streamDecrypt v.callees) s fun s' => GprAbi s s' ∧ streamDecryptAArch64.post s s' := by
  have hs' : streamCryptPre s := hs
  have run : ∀ (a c : List Byte) (icb : Block), a.length % 16 = (s.gpr .x3).toNat % 16 →
      c.length = (s.gpr .x4).toNat → WP isa (streamDecrypt v.callees) s (CrRun s a c icb
        (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)
        (xorKs (ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat) icb (s.gpr .x4).toNat
          (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat))) := fun a c icb ha hc =>
    cr_run (E := fun m => bytesAt m (s.gpr .x5) (s.gpr .x6).toNat)
      (O := fun m => xorKs (ciphOf m (s.gpr .x0) (s.gpr .x1).toNat) icb (s.gpr .x4).toNat
        (bytesAt m (s.gpr .x5) (s.gpr .x6).toNat)) hs' ha hc
      (fun m hf => by simp only [(crypt_inv hs' hf).2])
      (fun m hf => by simp only [(crypt_inv hs' hf).1, (crypt_inv hs' hf).2])
      (fun L h => decBody_ok L v h icb)
  have hz : (Spec.Gcm.zeros ((s.gpr .x3).toNat % 16)).length % 16 = (s.gpr .x3).toNat % 16 := by
    rw [Proof.Gcm.length_zeros, Nat.mod_mod]
  have hz' : (Spec.Gcm.zeros (s.gpr .x4).toNat).length = (s.gpr .x4).toNat := Proof.Gcm.length_zeros _
  obtain ⟨L, hds⟩ := lay_of_crypt hs'
  let ciph := ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat
  let h := ctxH s.mem (s.gpr .x0)
  refine WP.mono (WP.forall_det (P := fun (i : List Byte × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .x2) ciph h i.1 i.2.1 i.2.2 ∧
        s.gpr .x3 = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .x4).toNat = i.2.2.length)
    (Q := fun i s' =>
      StreamRepr s'.mem (s.gpr .x2) ciph h i.1 i.2.1 (i.2.2 ++ bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat) ∧
        bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat =
          (gctr ciph (inc32 (Spec.Gcm.j0 h i.1)) (i.2.2 ++ bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)).drop
            i.2.2.length)
    (run _ _ 0 hz hz') fun ⟨iv, a, c⟩ ⟨hr, hl, hc⟩ => ?_) fun s' ⟨r₀, hq⟩ =>
      ⟨r₀.1, fun iv a c hr hl hc => hq ⟨iv, a, c⟩ ⟨hr, hl, hc⟩⟩
  have hc : (s.gpr .x4).toNat = c.length := hc
  have hl : s.gpr .x3 = BitVec.ofNat 64 a.length := hl
  have ha : a.length % 16 = (s.gpr .x3).toNat % 16 := by rw [hl, toNat_mod16]
  refine WP.mono (run a c (inc32 (Spec.Gcm.j0 h iv)) ha hc.symm) fun s' ⟨_, hf, hpost⟩ => ?_
  show StreamRepr s'.mem (s.gpr .x2) ciph h iv a _ ∧ _
  obtain ⟨hj, habs, hctr⟩ := Proof.Gcm.streamRepr_iff.mp hr
  rw [← hc] at hctr
  obtain ⟨o₁, o₂, o₃⟩ := hpost habs hctr
  refine ⟨Proof.Gcm.streamRepr_iff.mpr ⟨?_, o₁, ?_⟩, ?_⟩
  · rw [← hj]; exact blockAt_frame hf (st0_crRun L hds)
  · rw [List.length_append, ← hc, length_bytesAt]; exact o₂
  · rw [Proof.Gcm.gctr_append, List.drop_left' (by rw [Proof.Gcm.length_gctr]), o₃, hc]; rfl

end VG.Proof.AesGcm.AArch64

end

end

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_encrypt` and `_decrypt` are constant time

Untrusted: everything here is checked by Lean. The entry and the exit by the
taint analysis; the bodies by `encBody_rel` and `decBody_rel`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

/-- `decAbs` in two runs, with the text in place or only read (`to`). -/
theorem decAbs_relG (v : GcmImpl) {to : Bool} {k₁ k₂ : Reg → BitVec 64} {R n P : Nat} {D : Addr}
    {a₁ a₂ c₁ c₂ : List Byte} {H₁ H₂ : Block} {σ₁ σ₂ : State} (h₁ : BodyInG to Ctx St W SP k₁ R n P D a₁ c₁ H₁ σ₁)
    (h₂ : BodyInG to Ctx St W SP k₂ R n P D a₂ c₂ H₂ σ₂) (hq : a₁.length % 16 = a₂.length % 16) :
    RelCT isa (Eq2 σ₁ σ₂) (decAbs v.callees) TT := by
  have k26₁ : k₁ .x26 = BitVec.ofNat 64 n := (h₁.kept .x26 (by decide)).symm.trans h₁.x26
  have k26₂ : k₂ .x26 = BitVec.ofNat 64 n := (h₂.kept .x26 (by decide)).symm.trans h₂.x26
  exact padArgs_relG L v h₁ h₂ hq fun τ₁ τ₂ e₁ e₂ g₁ g₂ a23₁ a23₂ a24₁ a24₂ a25₁ a25₂ d₁ d₂ =>
    textAbs_rel L v e₁ e₂ g₁ g₂ a23₁ a23₂ a24₁ a24₂ a25₁ a25₂
      ((g₁ .x26 (by decide)).trans k26₁) ((g₂ .x26 (by decide)).trans k26₂) (dataOk_of d₁) (dataOk_of d₂)

/-- `decAbs` in two runs. -/
theorem decAbs_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a₁ a₂ c₁ c₂ : List Byte}
    {H₁ H₂ : Block} {σ₁ σ₂ : State} (h₁ : BodyIn Ctx St W SP k₁ R n P D a₁ c₁ H₁ σ₁)
    (h₂ : BodyIn Ctx St W SP k₂ R n P D a₂ c₂ H₂ σ₂) (hq : a₁.length % 16 = a₂.length % 16) :
    RelCT isa (Eq2 σ₁ σ₂) (decAbs v.callees) TT :=
  decAbs_relG L v h₁ h₂ hq

/-- `decBody` in two runs. -/
theorem decBody_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a₁ a₂ c₁ c₂ : List Byte}
    {H₁ H₂ : Block} {σ₁ σ₂ : State} (h₁ : BodyIn Ctx St W SP k₁ R n P D a₁ c₁ H₁ σ₁)
    (h₂ : BodyIn Ctx St W SP k₂ R n P D a₂ c₂ H₂ σ₂) (hq : a₁.length % 16 = a₂.length % 16) :
    RelCT isa (Eq2 σ₁ σ₂) (decBody v.callees) TT := by
  have k22₁ : k₁ .x22 = BitVec.ofNat 64 R := (h₁.kept .x22 (by decide)).symm.trans h₁.x22
  have k26₁ : k₁ .x26 = BitVec.ofNat 64 n := (h₁.kept .x26 (by decide)).symm.trans h₁.x26
  have k28₁ : k₁ .x28 = D := (h₁.kept .x28 (by decide)).symm.trans h₁.x28
  have k22₂ : k₂ .x22 = BitVec.ofNat 64 R := (h₂.kept .x22 (by decide)).symm.trans h₂.x22
  have k26₂ : k₂ .x26 = BitVec.ofNat 64 n := (h₂.kept .x26 (by decide)).symm.trans h₂.x26
  have k28₂ : k₂ .x28 = D := (h₂.kept .x28 (by decide)).symm.trans h₂.x28
  refine rel_seq (decAbs_rel L v h₁ h₂ hq) (decAbs_ok L v h₁) (decAbs_ok L v h₂)
    fun τ₁ τ₂ ⟨e₁, kk₁, x25₁, _, rd₁, wr₁, _⟩ ⟨e₂, kk₂, x25₂, _, rd₂, wr₂, _⟩ => ?_
  refine rel_seq (rel_taint [.x26, .x28] (by rw [e₁.sp, e₂.sp])
      (by agree_tac [kk₁ .x26 (by decide), kk₂ .x26 (by decide), kk₁ .x28 (by decide),
        kk₂ .x28 (by decide), k26₁, k26₂, k28₁, k28₂]) ⟨_, by taint_decide⟩)
    (textPiece_ok kk₁ k26₁ k28₁) (textPiece_ok kk₂ k26₂ k28₂) fun τ₁ τ₂ ⟨p23₁, p24₁, rp₁⟩ ⟨p23₂, p24₂, rp₂⟩ => ?_
  have pk₁ := kk₁.of_others rp₁.others
  have pk₂ := kk₂.of_others rp₂.others
  exact crypt_rel L v
    ⟨e₁.of_regs rp₁, pk₁, (pk₁ .x22 (by decide)).trans k22₁, h₁.rounds, p23₁, p24₁,
      by rw [rp₁.others _ (by decide), x25₁], h₁.data.of_eq (by rw [rp₁.rd, rd₁]) (by rw [rp₁.wr, wr₁]), rfl⟩
    ⟨e₂.of_regs rp₂, pk₂, (pk₂ .x22 (by decide)).trans k22₂, h₂.rounds, p23₂, p24₂,
      by rw [rp₂.others _ (by decide), x25₂], h₂.data.of_eq (by rw [rp₂.rd, rd₂]) (by rw [rp₂.wr, wr₂]), rfl⟩

end

/-- The entry, a body and the exit, in two runs. -/
theorem cr_rel {body : Prog isa} {σ₁ σ₂ : State} (h₁ : streamCryptPre σ₁) (h₂ : streamCryptPre σ₂)
    (hq : streamCryptPub σ₁ σ₂)
    (hrel : ∀ {Ctx St W SP : Addr} {k₁ k₂ : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a₁ a₂ c₁ c₂ : List Byte}
      {H₁ H₂ : Block} {τ₁ τ₂ : State}, Lay Ctx St W → BodyIn Ctx St W SP k₁ R n P D a₁ c₁ H₁ τ₁ →
      BodyIn Ctx St W SP k₂ R n P D a₂ c₂ H₂ τ₂ → a₁.length % 16 = a₂.length % 16 →
      RelCT isa (Eq2 τ₁ τ₂) body TT)
    (hw : ∀ {Ctx St W SP : Addr} {k : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a c : List Byte} {H : Block}
      {τ : State}, Lay Ctx St W → BodyIn Ctx St W SP k R n P D a c H τ →
      WP isa body τ fun τ' => Env Ctx St W SP τ') :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block crEntry) (.seq body (.block restore))) TT := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp⟩ := hq
  simp only [streamCryptPre] at h₁ h₂
  rw [← q0, ← q1, ← q2, ← q5, ← q6, ← q7] at h₂
  obtain ⟨hrd₁, hwr₁, dcs, dcd, dcw, dsd, dsw, ddw, wc, ws, wd, ww, hR⟩ := h₁
  obtain ⟨hrd₂, hwr₂, -⟩ := h₂
  generalize hCtx : σ₁.gpr .x0 = Ctx at *
  generalize hSt : σ₁.gpr .x2 = St at *
  generalize hD : σ₁.gpr .x5 = D at *
  generalize hn : (σ₁.gpr .x6).toNat = n at *
  generalize hW : σ₁.gpr .x7 = W at *
  have L : Lay Ctx St W := Lay.of wc ws ww dcs dcw dsw
  have hlt : n < 2 ^ 64 := hn ▸ (σ₁.gpr .x6).isLt
  have perm (σ : State) (hrd : σ.rd = [⟨Ctx, 256⟩]) (hwr : σ.wr = [⟨St, 80⟩, ⟨D, n⟩, ⟨W, 2560⟩]) :
      Perm Ctx St W σ :=
    ⟨covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩
  have mk (σ σ' : State) (hwr : σ.wr = [⟨St, 80⟩, ⟨D, n⟩, ⟨W, 2560⟩]) (hR : rounds (σ.gpr .x1))
      (h : Env Ctx St W σ.sp σ' ∧ Kept σ'.gpr σ' ∧ σ'.gpr .x22 = BitVec.ofNat 64 (σ.gpr .x1).toNat ∧
        σ'.gpr .x25 = BitVec.ofNat 64 ((σ.gpr .x3).toNat % 16) ∧ σ'.gpr .x26 = BitVec.ofNat 64 n ∧
        σ'.gpr .x27 = BitVec.ofNat 64 (σ.gpr .x4).toNat ∧ σ'.gpr .x28 = D ∧ σ'.mem = savedMem σ.mem W σ.gpr ∧
        σ'.rd = σ.rd ∧ σ'.wr = σ.wr) :
      BodyIn Ctx St W σ.sp σ'.gpr (σ.gpr .x1).toNat n (σ.gpr .x4).toNat D
        (Spec.Gcm.zeros ((σ.gpr .x3).toNat % 16)) (Spec.Gcm.zeros (σ.gpr .x4).toNat)
        (blockAt σ'.mem (Ctx + BitVec.ofNat 64 240)) σ' := by
    obtain ⟨he, hk, x22, x25, x26, x27, x28, _, rd, wr⟩ := h
    exact ⟨he, hk, x22, hR, by rw [x25, hz_mod _ (Nat.mod_lt _ (by decide))], x26, x27, x28,
      Proof.Gcm.length_zeros _, (σ.gpr .x4).isLt,
      ⟨⟨covers_left (by rw [wr, hwr]; exact covers_of_mem (by simp)), hlt, wd, dsd.symm, ddw⟩,
        by rw [wr, hwr]; exact covers_of_mem (by simp), dcd⟩, rfl⟩
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] qsp
      (by agree_tac [hCtx, hSt, hD, hW, ← q0, q1, ← q2, q3, q4, ← q5, q6, ← q7]) ⟨_, by taint_decide⟩)
    (crEntry_ok hCtx hSt hD hn hW (perm σ₁ hrd₁ hwr₁))
    (crEntry_ok q0.symm q2.symm q5.symm (by rw [← q6, hn]) q7.symm (perm σ₂ hrd₂ hwr₂))
    fun τ₁ τ₂ a₁ a₂ => ?_
  have b₁ := mk σ₁ τ₁ hwr₁ hR a₁
  have b₂ := mk σ₂ τ₂ hwr₂ (by rw [← q1]; exact hR) a₂
  rw [← qsp, ← q1, ← q4] at b₂
  refine rel_seq (hrel L b₁ b₂ (by rw [Proof.Gcm.length_zeros, Proof.Gcm.length_zeros, Nat.mod_mod, Nat.mod_mod, q3]))
    (hw L b₁) (hw L b₂) fun τ₁ τ₂ e₁ e₂ => ?_
  exact rel_taint [.x19] (by rw [e₁.sp, e₂.sp]) (by agree_tac [e₁.x19, e₂.x19]) ⟨_, by taint_decide⟩

theorem streamEncrypt_ct (v : GcmImpl) :
    ConstantTime isa streamEncryptAArch64.pre streamEncryptAArch64.pub (streamEncrypt v.callees) :=
  ct_of fun _ _ h₁ h₂ hq => cr_rel h₁ h₂ hq (fun L b₁ b₂ hq => encBody_rel L v b₁ b₂ hq)
    (fun L b => WP.mono (encBody_ok L v b 0) fun _ h => h.env)

theorem streamDecrypt_ct (v : GcmImpl) :
    ConstantTime isa streamDecryptAArch64.pre streamDecryptAArch64.pub (streamDecrypt v.callees) :=
  ct_of fun _ _ h₁ h₂ hq => cr_rel h₁ h₂ hq (fun L b₁ b₂ hq => decBody_rel L v b₁ b₂ hq)
    (fun L b => WP.mono (decBody_ok L v b 0) fun _ h => h.env)

end VG.Proof.AesGcm.AArch64
