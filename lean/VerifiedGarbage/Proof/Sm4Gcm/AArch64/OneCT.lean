module

public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.FinCT
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.FinCT
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Contract
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Contract
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamInit
meta import VerifiedGarbage.Proof.AesGcm.AArch64.StreamInit
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Flush
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.Proof.AesGcm.AArch64.Save
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Flush
meta import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Spec.Gcm
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Save
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase

/-! ### `Sm4Gcm.AArch64.StreamCryptCT`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.AArch64.StreamCrypt`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on AArch64: `vg_sm4_gcm_stream_encrypt` and `vg_sm4_gcm_stream_decrypt`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers and sets up the body's arguments (`crEntry_ok`); the body
encrypts (`encBody_ok`) or decrypts (`decBody_ok`) and absorbs the
ciphertext, for any message so far of those lengths (`WP.forall_det`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghashInput StreamRepr gctr inc32)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- After the entry: the body's arguments. -/
theorem crEntry_ok {s : State} {Ctx St D W : Addr} {n : Nat} (hCtx : s.gpr .x0 = Ctx) (hSt : s.gpr .x1 = St)
    (hD : s.gpr .x4 = D) (hn : (s.gpr .x5).toNat = n) (hW : s.gpr .x6 = W) (hperm : Perm Ctx St W s) :
    WP isa (.block crEntry) s fun s' => Env Ctx St W s.sp s' ∧ Kept s'.gpr s' ∧
      s'.gpr .x25 = BitVec.ofNat 64 ((s.gpr .x2).toNat % 16) ∧ s'.gpr .x26 = BitVec.ofNat 64 n ∧
      s'.gpr .x27 = BitVec.ofNat 64 (s.gpr .x3).toNat ∧ s'.gpr .x28 = D ∧ s'.mem = savedMem s.mem W s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s .x6 hW hperm.w
  have hn' : s.gpr .x5 = BitVec.ofNat 64 n := by rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨s₂, run₂, x19₂, x20₂, x21₂, x26₂, x27₂, x28₂, x25₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x6, mov .x20 .x1, mov .x21 .x0, mov .x26 .x5, mov .x27 .x3, mov .x28 .x4,
        imm .x9 15, .logic .and .x .x25 .x2 .x9] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x20 = St ∧ s₂.gpr .x21 = Ctx ∧
      s₂.gpr .x26 = BitVec.ofNat 64 n ∧
      s₂.gpr .x27 = BitVec.ofNat 64 (s.gpr .x3).toNat ∧ s₂.gpr .x28 = D ∧
      s₂.gpr .x25 = BitVec.ofNat 64 ((s.gpr .x2).toNat % 16) ∧
      s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, g₁, hW]
    · simp [gpr_write, g₁, hSt]
    · simp [gpr_write, g₁, hCtx]
    · simp [gpr_write, g₁, hn']
    · simp [gpr_write, g₁]
    · simp [gpr_write, g₁, hD]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, g₁, BitVec.setWidth_eq]
      rw [show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  exact ⟨⟨x19₂, x20₂, x21₂, by rw [sp₂, sp₁], hperm.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])⟩,
    fun _ _ => rfl, x25₂, x26₂, x27₂, x28₂, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- What a run of `encrypt` or `decrypt` leaves, for the message `a`, `c` so far. -/
def CrRun (s : State) (a c : List Byte) (icb : Block) (e out : List Byte) (s' : State) : Prop :=
  GprAbi s s' ∧
  Frame (savedR (s.gpr .x6) :: bodyFrame (s.gpr .x1) (s.gpr .x6) s.sp (s.gpr .x4) (s.gpr .x5).toNat) s.mem s'.mem ∧
  (Absorbed s.mem (s.gpr .x1 + BitVec.ofNat 64 16) (s.gpr .x1 + BitVec.ofNat 64 32)
      (Spec.Gcm.ctxH s.mem (s.gpr .x0)) (ghashInput a c) →
    Ctr s.mem (s.gpr .x1 + BitVec.ofNat 64 48) (s.gpr .x1 + BitVec.ofNat 64 64)
      (ciphOf s.mem (s.gpr .x0)) icb (s.gpr .x3).toNat →
    Absorbed s'.mem (s.gpr .x1 + BitVec.ofNat 64 16) (s.gpr .x1 + BitVec.ofNat 64 32)
      (Spec.Gcm.ctxH s.mem (s.gpr .x0)) (ghashInput a (c ++ e)) ∧
    Ctr s'.mem (s.gpr .x1 + BitVec.ofNat 64 48) (s.gpr .x1 + BitVec.ofNat 64 64)
      (ciphOf s.mem (s.gpr .x0)) icb ((s.gpr .x3).toNat + (s.gpr .x5).toNat) ∧
    bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat = out)

/-- The entry, `body`, and the exit: what `body` does, moved to the entry
state. -/
theorem cr_run {body : Prog isa} {s : State} (hs : streamCryptPre s) {a c : List Byte}
    (ha : a.length % 16 = (s.gpr .x2).toNat % 16) (hc : c.length = (s.gpr .x3).toNat) {icb : Block}
    {E O : Mem → List Byte}
    (hE : ∀ m, Frame [savedR (s.gpr .x6)] s.mem m → E m = E s.mem)
    (hO : ∀ m, Frame [savedR (s.gpr .x6)] s.mem m → O m = O s.mem)
    (hb : ∀ {k : Reg → BitVec 64} {s₁ : State}, Lay (s.gpr .x0) (s.gpr .x1) (s.gpr .x6) s.sp →
      BodyIn (s.gpr .x0) (s.gpr .x1) (s.gpr .x6) s.sp k (s.gpr .x5).toNat (s.gpr .x3).toNat
        (s.gpr .x4) a c (Spec.Gcm.ctxH s.mem (s.gpr .x0)) s₁ →
      WP isa body s₁ (BodyOut (s.gpr .x0) (s.gpr .x1) (s.gpr .x6) s.sp k (s.gpr .x5).toNat
        (s.gpr .x3).toNat (s.gpr .x4) a c (Spec.Gcm.ctxH s.mem (s.gpr .x0)) icb (E s₁.mem) (O s₁.mem) s₁.mem)) :
    WP isa (.seq (.block crEntry) (.seq body (.block restore))) s (CrRun s a c icb (E s.mem) (O s.mem)) := by
  unfold CrRun
  simp only [streamCryptPre] at hs
  obtain ⟨hsp, hrd, hwr, dcs, dcd, dcw, dsd, dsw, ddw, sC, sS, sD, sW', wc, ws, wd, ww⟩ := hs
  generalize hCtx : s.gpr .x0 = Ctx at *
  generalize hSt : s.gpr .x1 = St at *
  generalize hD : s.gpr .x4 = D at *
  generalize hn : (s.gpr .x5).toNat = n at *
  generalize hW : s.gpr .x6 = W at *
  generalize hP : (s.gpr .x3).toNat = P at *
  have L : Lay Ctx St W s.sp := Lay.of wc ws ww dcs dcw dsw hsp sC sS sW'
  have perm : Perm Ctx St W s :=
    ⟨covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩
  have hlt : n < 2 ^ 64 := hn ▸ (s.gpr .x5).isLt
  have hPlt : P < 2 ^ 64 := hP ▸ (s.gpr .x3).isLt
  refine WP.seq (WP.mono (crEntry_ok hCtx hSt hD hn hW perm)
    fun s₁ ⟨he₁, hk₁, x25₁, x26₁, x27₁, x28₁, m₁, rd₁, wr₁⟩ => ?_)
  rw [hP] at x27₁
  have fsv : Frame [savedR W] s.mem s₁.mem := by rw [m₁]; exact savedMem_frame _ _ _
  have sW : Region.Sub (savedR W) ⟨W, 768⟩ := Lay.wSub (by decide)
  have hH : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = Spec.Gcm.ctxH s.mem Ctx :=
    blockAt_frame fsv (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (dcw.sub_left (Lay.ctxSub (by decide))).sub_right sW)
  have hdat : DataW Ctx St W s.sp s₁ D n :=
    ⟨⟨covers_left (by rw [wr₁, hwr]; exact covers_of_mem (by simp)), hlt, wd, dsd.symm, ddw⟩,
      by rw [wr₁, hwr]; exact covers_of_mem (by simp), dcd, sD⟩
  have hIn : BodyIn Ctx St W s.sp s₁.gpr n P D a c (Spec.Gcm.ctxH s.mem Ctx) s₁ :=
    ⟨he₁, hk₁, by rw [x25₁, ha], x26₁, x27₁, x28₁, hc, hPlt, hdat, hH⟩
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
  · have hc₁ : ciphOf s₁.mem Ctx = ciphOf s.mem Ctx :=
      ciph_frame fsv (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dcw.sub_right sW)
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

end VG.Proof.Sm4Gcm.AArch64

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput StreamRepr gctr inc32)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Spec.Gcm (ctxH)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- `J₀` is apart from what a run of `encrypt` or `decrypt` writes. -/
theorem st0_crRun {Ctx St W SP D : Addr} {n : Nat} (L : Lay Ctx St W SP) (hd : (⟨D, n⟩ : Region).Disjoint ⟨St, 80⟩) :
    ∀ r ∈ savedR W :: bodyFrame St W SP D n, (⟨St, 16⟩ : Region).Disjoint r := by
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
      · exact (L.ks.sub_right (Region.sub_prefix (by decide))).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact st0_disj L (by decide) (by decide)
    · exact st0_disj L (by decide) (by decide)
    · exact st0_w L ⟨by decide, by decide⟩

/-- What does not change in the entry's writes. -/
theorem crypt_inv {s : State} (hs : streamCryptPre s) {m : Mem} (hf : Frame [savedR (s.gpr .x6)] s.mem m) :
    ciphOf m (s.gpr .x0) = ciphOf s.mem (s.gpr .x0) ∧
      bytesAt m (s.gpr .x4) (s.gpr .x5).toNat = bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat := by
  simp only [streamCryptPre] at hs
  obtain ⟨-, -, -, -, -, dcw, -, -, ddw, -, -, -, -, -, -, -, -⟩ := hs
  have sW : Region.Sub (savedR (s.gpr .x6)) ⟨s.gpr .x6, 768⟩ := Lay.wSub (by decide)
  exact ⟨ciph_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dcw.sub_right sW),
    bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ddw.sub_right sW) (by omega_using [])⟩

theorem lay_of_crypt {s : State} (hs : streamCryptPre s) : Lay (s.gpr .x0) (s.gpr .x1) (s.gpr .x6) s.sp ∧
    (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region).Disjoint ⟨s.gpr .x1, 80⟩ := by
  simp only [streamCryptPre] at hs
  obtain ⟨hsp, -, -, dcs, -, dcw, dsd, dsw, -, sC, sS, -, sW', wc, ws, -, ww⟩ := hs
  exact ⟨Lay.of wc ws ww dcs dcw dsw hsp sC sS sW', dsd.symm⟩

theorem streamEncrypt_wp (v : GcmImpl) {s : State} (hs : streamEncryptAArch64.pre s) :
    WP isa (streamEncrypt v.callees) s fun s' => GprAbi s s' ∧ streamEncryptAArch64.post s s' := by
  have hs' : streamCryptPre s := hs
  have run : ∀ (a c : List Byte) (icb : Block), a.length % 16 = (s.gpr .x2).toNat % 16 →
      c.length = (s.gpr .x3).toNat → WP isa (streamEncrypt v.callees) s (CrRun s a c icb
        (xorKs (ciphOf s.mem (s.gpr .x0)) icb (s.gpr .x3).toNat
          (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat))
        (xorKs (ciphOf s.mem (s.gpr .x0)) icb (s.gpr .x3).toNat
          (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat))) := fun a c icb ha hc =>
    cr_run (E := fun m => xorKs (ciphOf m (s.gpr .x0)) icb (s.gpr .x3).toNat
        (bytesAt m (s.gpr .x4) (s.gpr .x5).toNat))
      (O := fun m => xorKs (ciphOf m (s.gpr .x0)) icb (s.gpr .x3).toNat
        (bytesAt m (s.gpr .x4) (s.gpr .x5).toNat)) hs' ha hc
      (fun m hf => by simp only [(crypt_inv hs' hf).1, (crypt_inv hs' hf).2])
      (fun m hf => by simp only [(crypt_inv hs' hf).1, (crypt_inv hs' hf).2])
      (fun L h => encBody_ok L v h icb)
  have hz : (Spec.Gcm.zeros ((s.gpr .x2).toNat % 16)).length % 16 = (s.gpr .x2).toNat % 16 := by
    rw [Proof.Gcm.length_zeros, Nat.mod_mod]
  have hz' : (Spec.Gcm.zeros (s.gpr .x3).toNat).length = (s.gpr .x3).toNat := Proof.Gcm.length_zeros _
  obtain ⟨L, hds⟩ := lay_of_crypt hs'
  let ciph := ctxCiph s.mem (s.gpr .x0)
  let h := ctxH s.mem (s.gpr .x0)
  refine WP.mono (WP.forall_det (P := fun (i : List Byte × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .x1) ciph h i.1 i.2.1 (gctr ciph (inc32 (Spec.Gcm.j0 h i.1)) i.2.2) ∧
        s.gpr .x2 = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .x3).toNat = i.2.2.length)
    (Q := fun i s' =>
      StreamRepr s'.mem (s.gpr .x1) ciph h i.1 i.2.1
          (gctr ciph (inc32 (Spec.Gcm.j0 h i.1)) (i.2.2 ++ bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)) ∧
        bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat =
          (gctr ciph (inc32 (Spec.Gcm.j0 h i.1)) (i.2.2 ++ bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)).drop
            i.2.2.length)
    (run _ _ 0 hz hz') fun ⟨iv, a, p⟩ ⟨hr, hl, hp⟩ => ?_) fun s' ⟨r₀, hq⟩ =>
      ⟨r₀.1, fun iv a p hr hl hp => hq ⟨iv, a, p⟩ ⟨hr, hl, hp⟩⟩
  have hp : (s.gpr .x3).toNat = p.length := hp
  have hl : s.gpr .x2 = BitVec.ofNat 64 a.length := hl
  have ha : a.length % 16 = (s.gpr .x2).toNat % 16 := by rw [hl, toNat_mod16]
  have hlen : (gctr ciph (inc32 (Spec.Gcm.j0 h iv)) p).length = (s.gpr .x3).toNat := by
    rw [Proof.Gcm.length_gctr, hp]
  refine WP.mono (run a _ (inc32 (Spec.Gcm.j0 h iv)) ha hlen) fun s' ⟨_, hf, hpost⟩ => ?_
  obtain ⟨hj, habs, hctr⟩ := Proof.Gcm.streamRepr_iff.mp hr
  rw [hlen] at hctr
  obtain ⟨o₁, o₂, o₃⟩ := hpost habs hctr
  have he : gctr ciph (inc32 (Spec.Gcm.j0 h iv)) (p ++ bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) =
      gctr ciph (inc32 (Spec.Gcm.j0 h iv)) p ++ xorKs (ciphOf s.mem (s.gpr .x0))
        (inc32 (Spec.Gcm.j0 h iv)) (s.gpr .x3).toNat (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) := by
    rw [Proof.Gcm.gctr_append, hp]; rfl
  show StreamRepr s'.mem (s.gpr .x1) ciph h iv a _ ∧ _
  rw [he]
  refine ⟨Proof.Gcm.streamRepr_iff.mpr ⟨?_, o₁, ?_⟩, ?_⟩
  · rw [← hj]; exact blockAt_frame hf (st0_crRun L hds)
  · rw [List.length_append, hlen, Proof.Gcm.length_xorKs, length_bytesAt]; exact o₂
  · rw [List.drop_left' (by rw [hlen, hp]), o₃]

theorem streamDecrypt_wp (v : GcmImpl) {s : State} (hs : streamDecryptAArch64.pre s) :
    WP isa (streamDecrypt v.callees) s fun s' => GprAbi s s' ∧ streamDecryptAArch64.post s s' := by
  have hs' : streamCryptPre s := hs
  have run : ∀ (a c : List Byte) (icb : Block), a.length % 16 = (s.gpr .x2).toNat % 16 →
      c.length = (s.gpr .x3).toNat → WP isa (streamDecrypt v.callees) s (CrRun s a c icb
        (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
        (xorKs (ciphOf s.mem (s.gpr .x0)) icb (s.gpr .x3).toNat
          (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat))) := fun a c icb ha hc =>
    cr_run (E := fun m => bytesAt m (s.gpr .x4) (s.gpr .x5).toNat)
      (O := fun m => xorKs (ciphOf m (s.gpr .x0)) icb (s.gpr .x3).toNat
        (bytesAt m (s.gpr .x4) (s.gpr .x5).toNat)) hs' ha hc
      (fun m hf => by simp only [(crypt_inv hs' hf).2])
      (fun m hf => by simp only [(crypt_inv hs' hf).1, (crypt_inv hs' hf).2])
      (fun L h => decBody_ok L v h icb)
  have hz : (Spec.Gcm.zeros ((s.gpr .x2).toNat % 16)).length % 16 = (s.gpr .x2).toNat % 16 := by
    rw [Proof.Gcm.length_zeros, Nat.mod_mod]
  have hz' : (Spec.Gcm.zeros (s.gpr .x3).toNat).length = (s.gpr .x3).toNat := Proof.Gcm.length_zeros _
  obtain ⟨L, hds⟩ := lay_of_crypt hs'
  let ciph := ctxCiph s.mem (s.gpr .x0)
  let h := ctxH s.mem (s.gpr .x0)
  refine WP.mono (WP.forall_det (P := fun (i : List Byte × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .x1) ciph h i.1 i.2.1 i.2.2 ∧
        s.gpr .x2 = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .x3).toNat = i.2.2.length)
    (Q := fun i s' =>
      StreamRepr s'.mem (s.gpr .x1) ciph h i.1 i.2.1 (i.2.2 ++ bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) ∧
        bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat =
          (gctr ciph (inc32 (Spec.Gcm.j0 h i.1)) (i.2.2 ++ bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)).drop
            i.2.2.length)
    (run _ _ 0 hz hz') fun ⟨iv, a, c⟩ ⟨hr, hl, hc⟩ => ?_) fun s' ⟨r₀, hq⟩ =>
      ⟨r₀.1, fun iv a c hr hl hc => hq ⟨iv, a, c⟩ ⟨hr, hl, hc⟩⟩
  have hc : (s.gpr .x3).toNat = c.length := hc
  have hl : s.gpr .x2 = BitVec.ofNat 64 a.length := hl
  have ha : a.length % 16 = (s.gpr .x2).toNat % 16 := by rw [hl, toNat_mod16]
  refine WP.mono (run a c (inc32 (Spec.Gcm.j0 h iv)) ha hc.symm) fun s' ⟨_, hf, hpost⟩ => ?_
  show StreamRepr s'.mem (s.gpr .x1) ciph h iv a _ ∧ _
  obtain ⟨hj, habs, hctr⟩ := Proof.Gcm.streamRepr_iff.mp hr
  rw [← hc] at hctr
  obtain ⟨o₁, o₂, o₃⟩ := hpost habs hctr
  refine ⟨Proof.Gcm.streamRepr_iff.mpr ⟨?_, o₁, ?_⟩, ?_⟩
  · rw [← hj]; exact blockAt_frame hf (st0_crRun L hds)
  · rw [List.length_append, ← hc, length_bytesAt]; exact o₂
  · rw [Proof.Gcm.gctr_append, List.drop_left' (by rw [Proof.Gcm.length_gctr]), o₃, hc]; rfl

end VG.Proof.Sm4Gcm.AArch64

end

end

/-! ### `Sm4Gcm.AArch64.Open`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.AArch64.Seal`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.AArch64.OneShot`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.AArch64.Front`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on AArch64: `J₀` and the additional data of `seal` and `open`

Untrusted: everything here is checked by Lean. After the entry, `j0` starts
the state at `W + 16` for the nonce, `oneAad` absorbs the additional data and
`encPrep` sets up the text's arguments from the slots the entry wrote
(`front_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt inc32)
open VG.Proof.Gcm (Absorbed)

/-- The regions `j0` and `oneAad` write. -/
abbrev frontFrame (St W : Addr) : List Region := j0Frame St W ++ absFrame St W 16

/-- The slots stay where they are, outside a frame apart from them. -/
theorem slot_kept {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {W : Addr}
    (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r) {d : Nat} (h₁ : 216 ≤ d)
    (h₂ : d + 8 ≤ 256) : m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub _ h₁ (by omega_using [h₂]))) (by decide)

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

theorem slots_j0Frame : ∀ r ∈ j0Frame St W, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 80) (d := 216) (k := 40) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem slots_absFrame : ∀ r ∈ absFrame St W 16, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem slots_frontFrame : ∀ r ∈ frontFrame St W, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact slots_j0Frame L r hr
  · exact slots_absFrame L r hr

theorem saved_frontFrame : ∀ r ∈ frontFrame St W, (savedR W).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact saved_j0Frame L r hr
  · exact saved_absFrame L (.inr rfl) r hr

/-- After `encPrep`, from `s₀`. -/
structure Front (Ctx St W SP : Addr) (H : Block) (iv a : List Byte) (D : Addr) (n : Nat) (s₀ : State)
    (s : State) : Prop where
  env : Env Ctx St W SP s
  x22 : s.gpr .x22 = s₀.gpr .x22
  x25 : s.gpr .x25 = BitVec.ofNat 64 (a.length % 16)
  x26 : s.gpr .x26 = BitVec.ofNat 64 n
  x27 : s.gpr .x27 = 0
  x28 : s.gpr .x28 = D
  j0 : blockAt s.mem St = Spec.Gcm.j0 H iv
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  cb : blockAt s.mem (St + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 H iv)
  abs : Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H a
  frame : Frame (frontFrame St W) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- `j0`, `oneAad` and `encPrep`. -/
theorem front_ok (v : GcmImpl) {s₀ : State} {k : Reg → BitVec 64} {H : Block} {Np A D : Addr} {nl al n : Nat}
    (he : Env Ctx St W SP s₀) (hk : Kept k s₀) (h23 : s₀.gpr .x23 = Np) (h24 : s₀.gpr .x24 = BitVec.ofNat 64 nl)
    (h26 : s₀.gpr .x26 = BitVec.ofNat 64 nl) (h27 : s₀.gpr .x27 = 0)
    (hnon : DataOk St W s₀ Np nl) (haad : DataOk St W s₀ A al)
    (hH : blockAt s₀.mem (Ctx + BitVec.ofNat 64 240) = H)
    (sA : s₀.mem.readW (W + BitVec.ofNat 64 216) 64 = A)
    (sL : s₀.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (sD : s₀.mem.readW (W + BitVec.ofNat 64 232) 64 = D)
    (sN : s₀.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n)
    {rest : Prog isa} {Q : State → Prop}
    (hr : ∀ s', Front Ctx St W SP H (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) D n s₀ s' → WP isa rest s' Q) :
    WP isa (.seq (j0 v.callees) (.seq (oneAad v.callees) (.seq (.block encPrep) rest))) s₀ Q := by
  have hlt := haad.lt
  refine WP.seq (WP.mono (WP.with_rdwr (j0_ok L v ⟨he, hk, h23, h24, h26, h27, hnon, hH⟩))
    fun s₁ ⟨h₁, rd₁, wr₁⟩ => ?_)
  have r₁ (d : Nat) (h : d + 8 ≤ 768) := h₁.env.perm.wR h
  obtain ⟨s₂, run₂, x23₂, x24₂, x25₂, r₂⟩ : ∃ s₂, runBlock isa [.ldr .x .x23 .x19 aadO, .ldr .x .x24 .x19 alenO,
      imm .x25 0] s₁ = some s₂ ∧ s₂.gpr .x23 = A ∧ s₂.gpr .x24 = BitVec.ofNat 64 al ∧
      s₂.gpr .x25 = BitVec.ofNat 64 0 ∧ Regs [.x23, .x24, .x25] s₁ s₂ := by
    have e₁ := slot_kept h₁.frame (slots_j0Frame L) (d := 216) (by decide) (by decide)
    have e₂ := slot_kept h₁.frame (slots_j0Frame L) (d := 224) (by decide) (by decide)
    rw [sA] at e₁
    rw [sL] at e₂
    have q₁ := r₁ 216 (by decide)
    have q₂ := r₁ 224 (by decide)
    refine ⟨_, by arun [h₁.env.x19, q₁, q₂], ?_⟩
    refine ⟨?_, ?_, by simp [gpr_write], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; rw [← e₁]; rfl
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; rw [← e₂]; rfl
  refine WP.seq (WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩))
  have he₂ := h₁.env.of_regs r₂
  have hk₂ := h₁.kept.of_others r₂.others
  have hd₂ : DataOk St W s₂ A al := haad.of_eq (by rw [r₂.rd, rd₁]) (by rw [r₂.wr, wr₁])
  have hIn : AbsIn Ctx St W SP k H [] A al 0 s₂ :=
    ⟨he₂, hk₂, x23₂, x24₂, x25₂, rfl, hd₂, by rw [r₂.mem]; exact h₁.hH⟩
  refine WP.mono (WP.with_rdwr (absorbAl_ok L (.inr rfl) v hIn)) fun s₃ ⟨h₃, rd₃, wr₃⟩ => ?_
  have f₃ : Frame (frontFrame St W) s₀.mem s₃.mem :=
    (h₁.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩).trans
      (by rw [← r₂.mem]; exact h₃.frame.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩)
  have q (d : Nat) (h : d + 8 ≤ 768) := h₃.env.perm.wR h
  obtain ⟨s₄, run₄, x25₄, x26₄, x27₄, x28₄, r₄⟩ : ∃ s₄, runBlock isa encPrep s₃ = some s₄ ∧
      s₄.gpr .x25 = BitVec.ofNat 64 (al % 16) ∧ s₄.gpr .x26 = BitVec.ofNat 64 n ∧ s₄.gpr .x27 = 0 ∧
      s₄.gpr .x28 = D ∧ Regs [.x9, .x10, .x25, .x26, .x27, .x28] s₃ s₄ := by
    have e₂ := slot_kept f₃ (slots_frontFrame L) (d := 224) (by decide) (by decide)
    have e₃ := slot_kept f₃ (slots_frontFrame L) (d := 232) (by decide) (by decide)
    have e₄ := slot_kept f₃ (slots_frontFrame L) (d := 240) (by decide) (by decide)
    rw [sL] at e₂
    rw [sD] at e₃
    rw [sN] at e₄
    have q₂ := q 224 (by decide)
    have q₃ := q 232 (by decide)
    have q₄ := q 240 (by decide)
    refine ⟨_, by simp only [encPrep]; arun [h₃.env.x19, q₂, q₃, q₄], ?_⟩
    refine ⟨?_, ?_, by simp [gpr_write], ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
      rw [show s₃.mem.read (W + 224#64) 8 = s₃.mem.readW (W + BitVec.ofNat 64 224) 64 from rfl, e₂,
        show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15, toNat_ofNat_of_lt hlt]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
      rw [show s₃.mem.read (W + 240#64) 8 = s₃.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl, e₄]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
      rw [show s₃.mem.read (W + 232#64) 8 = s₃.mem.readW (W + BitVec.ofNat 64 232) 64 from rfl, e₃]
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, hr s₄ ⟨h₃.env.of_regs r₄, ?_, ?_, x26₄, x27₄, x28₄, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩)
  · rw [r₄.others _ (by decide), h₃.kept .x22 (by decide), ← hk .x22 (by decide)]
  · rw [x25₄, length_bytesAt]
  · rw [r₄.mem, blockAt_frame h₃.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact st0_disj L (by decide) (by decide)
      · exact st0_disj L (by decide) (by decide)
      · exact st0_w L ⟨by decide, by decide⟩), r₂.mem, h₁.j0]
  · rw [r₄.mem, blockAt_frame h₃.frame (ctx_absFrame L (.inr rfl)), r₂.mem, h₁.hH]
  · rw [r₄.mem, blockAt_frame h₃.frame (fun r hr => (ctr_absFrame L r hr).sub_left
      (Region.sub_prefix (by decide))), r₂.mem, h₁.cb]
  · rw [r₄.mem]
    have := h₃.abs (Proof.Gcm.absorbed_nil H (by rw [r₂.mem]; exact h₁.y))
    rw [List.nil_append, r₂.mem, bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact haad.st
      · exact haad.w.sub_right (Lay.wSub (by decide))
      · exact haad.w.sub_right (Lay.wSub (by decide))) (by omega_using [hlt])] at this
    exact this
  · rw [r₄.mem]; exact f₃
  · rw [r₄.rd, rd₃, r₂.rd, rd₁]
  · rw [r₄.wr, wr₃, r₂.wr, wr₁]

end

end VG.Proof.Sm4Gcm.AArch64

end

end

/-! ### `Sm4Gcm.AArch64.OneEntry`, which only this module used -/

section

/-!
# SM4-GCM on AArch64: the entry of `seal` and `open`

Untrusted: everything here is checked by Lean. `work` comes from the stack
(`ldrSp_ok`); the entry saves our caller's registers there, keeps the arguments it needs
later at `W + 216` (`oneEntry_ok`, `OneE`), and puts the state at
`W + 16` (`oneLay`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- The memory after the entry: the registers saved and the arguments kept. -/
def entryMem (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Mem :=
  ((((savedMem m W g).writeW (W + BitVec.ofNat 64 216) (g .x3)).writeW (W + BitVec.ofNat 64 224) (g .x4)).writeW
    (W + BitVec.ofNat 64 232) (g .x5)).writeW (W + BitVec.ofNat 64 240) (g .x6)

/-- What the entry keeps at `W + 128`. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 128⟩

theorem entry_contains (W : Addr) {d : Nat} (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 256) :
    (entryR W).Contains (W + BitVec.ofNat 64 d) 8 := by
  rw [show W + BitVec.ofNat 64 d = (W + BitVec.ofNat 64 128) + BitVec.ofNat 64 (d - 128) from
    (Offset.add_add_eq W (by omega_using [h₁])).symm]
  exact Offset.contains_base _ (by omega_using [h₂]) (by omega_using [h₂])

theorem entryMem_frame (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Frame [entryR W] m (entryMem m W g) := by
  have c (d : Nat) (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 256) := entry_contains W h₁ h₂
  exact (((((savedMem_frame m W g).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩).writeW
    (List.mem_singleton_self _) _ (c 216 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 224 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 232 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 240 (by decide) (by decide))

theorem entryMem_saved (m : Mem) (W : Addr) {g : Reg → BitVec 64} {s₀ : State}
    (hg : ∀ p ∈ saved, g p.1 = s₀.gpr p.1) : SavedAt (entryMem m W g) W s₀ := by
  have h₀ : SavedAt (savedMem m W g) W s₀ := fun p hp => (savedMem_slot m W g p hp).trans (hg p hp)
  refine h₀.frame (rs := [⟨W + BitVec.ofNat 64 216, 32⟩]) ?_ ?_
  · have c (d : Nat) (h₁ : 216 ≤ d) (h₂ : d + 8 ≤ 248) :
        (⟨W + BitVec.ofNat 64 216, 32⟩ : Region).Contains (W + BitVec.ofNat 64 d) 8 := by
      rw [show W + BitVec.ofNat 64 d = (W + BitVec.ofNat 64 216) + BitVec.ofNat 64 (d - 216) from
        (Offset.add_add_eq W (by omega_using [h₁])).symm]
      exact Offset.contains_base _ (by omega_using [h₂]) (by omega_using [h₂])
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 216 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 224 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 232 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 240 (by decide) (by decide))
  · intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)

theorem entryMem_slot (m : Mem) (W : Addr) (g : Reg → BitVec 64) :
    (entryMem m W g).readW (W + BitVec.ofNat 64 216) 64 = g .x3 ∧
    (entryMem m W g).readW (W + BitVec.ofNat 64 224) 64 = g .x4 ∧
    (entryMem m W g).readW (W + BitVec.ofNat 64 232) 64 = g .x5 ∧
    (entryMem m W g).readW (W + BitVec.ofNat 64 240) 64 = g .x6 := by
  simp only [entryMem]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  repeat (first
    | rw [Mem.readW_writeW_self64]
    | rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide)])

/-- The load of a stack argument, at `sp + k`. -/
theorem ldrSp_ok {s : State} {t : Reg} {k : Nat} {V : BitVec 64} (hk : k % 8 = 0 ∧ k < 32768)
    (hV : s.mem.readW (s.sp + BitVec.ofNat 64 k) 64 = V)
    (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 k) 8) :
    ∃ s', runBlock isa [.ldrSp t k] s = some s' ∧ s'.gpr t = V ∧ (∀ r, r ≠ t → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by arun [hsp, hk], ?_⟩
  refine ⟨?_, fun r hr => by simp [gpr_write, hr], rfl, rfl, rfl, rfl⟩
  rw [← hV]
  simp [gpr_write, Mem.readW]

/-- After the entry, with `work` at `sp + k`. -/
theorem oneEntry_ok {s : State} {Ctx W : Addr} {k : Nat} (hk : k % 8 = 0 ∧ k < 32768)
    (hW : s.mem.readW (s.sp + BitVec.ofNat 64 k) 64 = W)
    (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 k) 8) (hCtx : s.gpr .x0 = Ctx)
    (hperm : Perm Ctx (W + BitVec.ofNat 64 16) W s) :
    WP isa (.block (oneEntry k)) s fun s' => Env Ctx (W + BitVec.ofNat 64 16) W s.sp s' ∧
      s'.gpr .x23 = s.gpr .x1 ∧ s'.gpr .x24 = s.gpr .x2 ∧
      s'.gpr .x26 = s.gpr .x2 ∧ s'.gpr .x27 = 0 ∧ s'.gpr .x7 = s.gpr .x7 ∧
      s'.mem.readW (W + BitVec.ofNat 64 216) 64 = s.gpr .x3 ∧
      s'.mem.readW (W + BitVec.ofNat 64 224) 64 = s.gpr .x4 ∧
      s'.mem.readW (W + BitVec.ofNat 64 232) 64 = s.gpr .x5 ∧
      s'.mem.readW (W + BitVec.ofNat 64 240) 64 = s.gpr .x6 ∧
      Frame [entryR W] s.mem s'.mem ∧ SavedAt s'.mem W s ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₀, run₀, x9₀, g₀, sp₀, m₀, rd₀, wr₀⟩ := ldrSp_ok (t := .x9) hk hW hsp
  have hperm₀ : Perm Ctx (W + BitVec.ofNat 64 16) W s₀ := hperm.of_eq rd₀ wr₀
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s₀ .x9 x9₀ hperm₀.w
  have w (d : Nat) (h : d + 8 ≤ 768) := in_off hperm₀.w h (by decide)
  rw [← wr₁] at w
  obtain ⟨s₂, run₂, x19₂, x20₂, x21₂, x23₂, x24₂, x26₂, x27₂, x7₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x9, ptr .x20 .x19 16, mov .x21 .x0, .str .x .x3 .x19 aadO,
        .str .x .x4 .x19 alenO, .str .x .x5 .x19 dataO, .str .x .x6 .x19 lenO, mov .x23 .x1,
        mov .x24 .x2, mov .x26 .x2, imm .x27 0] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x20 = W + BitVec.ofNat 64 16 ∧ s₂.gpr .x21 = Ctx ∧
      s₂.gpr .x23 = s.gpr .x1 ∧ s₂.gpr .x24 = s.gpr .x2 ∧ s₂.gpr .x26 = s.gpr .x2 ∧ s₂.gpr .x27 = 0 ∧ s₂.gpr .x7 = s.gpr .x7 ∧
      s₂.sp = s₁.sp ∧
      s₂.mem = (((s₁.mem.writeW (W + BitVec.ofNat 64 216) (s.gpr .x3)).writeW (W + BitVec.ofNat 64 224)
        (s.gpr .x4)).writeW (W + BitVec.ofNat 64 232) (s.gpr .x5)).writeW (W + BitVec.ofNat 64 240) (s.gpr .x6) ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have gx : ∀ r, r ≠ .x9 → s₁.gpr r = s.gpr r := fun r hr => by rw [g₁, g₀ r hr]
    have x9₁ : s₁.gpr .x9 = W := by rw [g₁, x9₀]
    have w₁ := w 216 (by decide)
    have w₂ := w 224 (by decide)
    have w₃ := w 232 (by decide)
    have w₄ := w 240 (by decide)
    refine ⟨_, by arun [x9₁, BitVec.add_zero, w₁, w₂, w₃, w₄], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, rfl, rfl⟩
    · simp [gpr_write, x9₁]
    · simp [gpr_write, x9₁]
    · simp [gpr_write, gx .x0 (by decide), hCtx]
    · simp [gpr_write, gx .x1 (by decide)]
    · simp [gpr_write, gx .x2 (by decide)]
    · simp [gpr_write, gx .x2 (by decide)]
    · simp [gpr_write]
    · simp [gpr_write, gx .x7 (by decide)]
    · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, gpr_write, ite_true, ite_false, reduceCtorEq,
        gx .x3 (by decide), gx .x4 (by decide), gx .x5 (by decide), gx .x6 (by decide), x9₁]
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s₀, run₀, WP.of_runBlock ⟨s₁, run₁,
    WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩⟩))
  have hm : s₂.mem = entryMem s.mem W s₀.gpr := by
    rw [m₂, m₁, m₀, entryMem, g₀ .x3 (by decide), g₀ .x4 (by decide), g₀ .x5 (by decide), g₀ .x6 (by decide)]
  obtain ⟨e₁, e₂, e₃, e₄⟩ := entryMem_slot s.mem W s₀.gpr
  rw [g₀ .x3 (by decide)] at e₁
  rw [g₀ .x4 (by decide)] at e₂
  rw [g₀ .x5 (by decide)] at e₃
  rw [g₀ .x6 (by decide)] at e₄
  refine ⟨⟨x19₂, x20₂, x21₂, by rw [sp₂, sp₁, sp₀], hperm.of_eq (by rw [rd₂, rd₁, rd₀]) (by rw [wr₂, wr₁, wr₀])⟩,
    x23₂, x24₂, x26₂, x27₂, x7₂, by rw [hm]; exact e₁, by rw [hm]; exact e₂, by rw [hm]; exact e₃,
    by rw [hm]; exact e₄, by rw [hm]; exact entryMem_frame _ _ _,
    by rw [hm]; exact entryMem_saved _ _ fun p hp => g₀ p.1 (by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [rd₂, rd₁, rd₀], by rw [wr₂, wr₁, wr₀]⟩

end VG.Proof.Sm4Gcm.AArch64

end

end


/-!
# SM4-GCM on AArch64: what `seal` and `open` share

Untrusted: everything here is checked by Lean. The layout of a one-shot call
(`oneLay`): the state at `W + 16`, inside `work`; everything the pieces
write is inside `work`, but for the data (`*_work`) and the tag.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- `work`. -/
abbrev workR (W : Addr) : Region := ⟨W, 768⟩

theorem stW {W : Addr} {d k : Nat} (h : d + k ≤ 80) :
    Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ (workR W) := by
  rw [add_ofNat_assoc]; exact Lay.wSub (by omega_using [h])

theorem keep_of_sub {rs : List Region} {W : Addr} (hs : ∀ r ∈ rs, Region.Sub r (workR W)) {X : Region}
    (hX : X.Disjoint (workR W)) : ∀ r ∈ rs, X.Disjoint r := fun r hr => hX.sub_right (hs r hr)

theorem entryR_work (W : Addr) : ∀ r ∈ [entryR W], Region.Sub r (workR W) := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)

theorem frontFrame_work (W : Addr) : ∀ r ∈ frontFrame (W + BitVec.ofNat 64 16) W, Region.Sub r (workR W) := by
  intro r hr
  simp only [frontFrame, j0Frame, absFrame, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Lay.wSub (by decide)
  · exact Lay.wSub (by decide)
  · exact Lay.wSub (by decide)
  · exact stW (by decide)
  · exact stW (by decide)
  · exact Lay.wSub (by decide)

theorem finFrame_work (W SP : Addr) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ finFrame (W + BitVec.ofNat 64 16) W SP o, Region.Sub r (workR W) ∨ r = stk SP := by
  intro r hr
  simp only [finFrame, tFrame, tagFrame, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (stW (by decide))
  · exact .inl (Lay.wSub (by decide))
  · exact .inl (Lay.wSub (by decide))
  · exact .inl (Lay.wSub (by decide))
  · exact .inl (Lay.wSub (by decide))
  · exact .inl (Lay.wSub (by omega_using [ho]))
  · exact .inl (Lay.wSub (by decide))
  · exact .inr rfl

theorem keep_fin {W SP : Addr} {o : Nat} (ho : o = 0 ∨ o = 112) {X : Region} (hX : X.Disjoint (workR W))
    (hS : X.Disjoint (stk SP)) : ∀ r ∈ finFrame (W + BitVec.ofNat 64 16) W SP o, X.Disjoint r := fun r hr => by
  rcases finFrame_work W SP ho r hr with h | rfl
  · exact hX.sub_right h
  · exact hS

/-- The regions a body writes: in `work`, the data, or the callee's stack. -/
theorem bodyFrame_work (W SP D : Addr) (n : Nat) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W SP D n,
      Region.Sub r (workR W) ∨ r = ⟨D, n⟩ ∨ r = stk SP := by
  intro r hr
  simp only [bodyFrame, tFrame, crFrame, absFrame, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (stW (by decide))
  · exact .inl (Lay.wSub (by decide))
  · exact .inl (Lay.wSub (by decide))
  · exact .inr (.inl rfl)
  · exact .inl (stW (by decide))
  · exact .inr (.inr rfl)
  · exact .inl (stW (by decide))
  · exact .inl (stW (by decide))
  · exact .inl (Lay.wSub (by decide))

theorem keep_body {W SP D : Addr} {n : Nat} {X : Region} (hX : X.Disjoint (workR W)) (hD : X.Disjoint ⟨D, n⟩)
    (hS : X.Disjoint (stk SP)) : ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W SP D n, X.Disjoint r := fun r hr => by
  rcases bodyFrame_work W SP D n r hr with h | rfl | rfl
  · exact hX.sub_right h
  · exact hD
  · exact hS

/-- What `seal` and `open` share: `ctx`, `nonce`, `aad`, the `n` stack
arguments, `data`, and `work` the `w`-th of them. -/
def oneCore (n w : Nat) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let nonce : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
  let aad : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  let data : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let work : Region := ⟨stackArg s w, 768⟩
  ctx ∈ s.rd ∧ nonce ∈ s.rd ∧ aad ∈ s.rd ∧ args s n ∈ s.rd ∧ data ∈ s.wr ∧ work ∈ s.wr ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s n) ∧ work.Disjoint (args s n) ∧
    (stk s.sp).Disjoint ctx ∧ (stk s.sp).Disjoint nonce ∧ (stk s.sp).Disjoint aad ∧
    (stk s.sp).Disjoint data ∧ (stk s.sp).Disjoint work ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧
    (stackArg s w).toNat + 768 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 * n ≤ 2 ^ 64 ∧ 3264 ≤ s.sp.toNat

/-- What `oneCore` gives, with `work` the `w`-th of the `n` arguments on the stack. -/
structure OneLay (s : State) (n w : Nat) : Prop where
  lay : Lay (s.gpr .x0) (stackArg s w + BitVec.ofNat 64 16) (stackArg s w) s.sp
  perm : Perm (s.gpr .x0) (stackArg s w + BitVec.ofNat 64 16) (stackArg s w) s
  hsp : ∀ i < n, InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * i)) 8
  nonce : (⟨s.gpr .x1, (s.gpr .x2).toNat⟩ : Region).Disjoint (workR (stackArg s w))
  aad : (⟨s.gpr .x3, (s.gpr .x4).toNat⟩ : Region).Disjoint (workR (stackArg s w))
  data : (⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region).Disjoint (workR (stackArg s w))
  ctx : (⟨s.gpr .x0, 256⟩ : Region).Disjoint (workR (stackArg s w))
  args : (args s n).Disjoint (workR (stackArg s w))
  nd : (⟨s.gpr .x1, (s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  ad : (⟨s.gpr .x3, (s.gpr .x4).toNat⟩ : Region).Disjoint ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  cd : (⟨s.gpr .x0, 256⟩ : Region).Disjoint ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  nw : (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64
  aw : (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64
  dw : (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64
  kn : (stk s.sp).Disjoint ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
  ka : (stk s.sp).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  kd : (stk s.sp).Disjoint ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  nonceR : Covers [⟨s.gpr .x1, (s.gpr .x2).toNat⟩] (s.rd ++ s.wr)
  aadR : Covers [⟨s.gpr .x3, (s.gpr .x4).toNat⟩] (s.rd ++ s.wr)
  dataW : Covers [⟨s.gpr .x5, (s.gpr .x6).toNat⟩] s.wr

theorem oneLay {s : State} {n w : Nat} (hs : oneCore n w s) : OneLay s n w := by
  simp only [oneCore] at hs
  sig_split hs
  rename_i mc mn ma mg md mw dcd dcw dnd dnw dad daw ddw dda dwa kc kn ka kd kw wc wn wa wd ww wsp
  have hsp := hs
  clear hs
  have sub16 : Region.Sub ⟨stackArg s w + BitVec.ofNat 64 16, 80⟩ (workR (stackArg s w)) := Lay.wSub (by decide)
  refine ⟨⟨wc, ?_, ww, dcw.sub_right sub16, dcw, ?_, ?_, hsp, kc, kw.sub_right sub16, kw⟩,
    ⟨covers_mem (List.mem_append_left _ mc),
      covers_off (k := 768) (covers_of_mem mw) (show 16 + 80 ≤ 768 by decide) (by decide),
      covers_of_mem mw⟩,
    fun i hi => ?_, dnw, daw, ddw, dcw, dwa.symm, dnd, dad, dcd, wn, wa, wd, kn, ka, kd,
    covers_mem (List.mem_append_left _ mn), covers_mem (List.mem_append_left _ ma), covers_of_mem md⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16) (by decide), Nat.mod_eq_of_lt (by omega_using [ww])]
    omega_using [ww]
  · simpa using Offset.disjoint (stackArg s w) (d := 16) (n := 80) (e := 0) (k := 16) (.inr (by decide))
      (by decide) (by decide)
  · exact Offset.disjoint (stackArg s w) (d := 16) (n := 80) (e := 96) (k := 672) (.inl (by decide))
      (by decide) (by decide)
  · refine ⟨args s n, List.mem_append_left _ mg, ?_⟩
    have e : stackArgAddr s 0 = s.sp := by simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    simp only [args, e]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [wsp, hi])

end VG.Proof.Sm4Gcm.AArch64

end

end

/-!
# SM4-GCM on AArch64: `vg_sm4_gcm_seal`

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/AArch64/Seal.lean`): the entry and `front_ok` start the state
at `W + 16` and absorb the additional data, and keep `tag` (`x7`) at
`W + 248`; `encBody` encrypts the data and absorbs the ciphertext, `finBody 0`
writes the tag to `W`, and `tagOut` copies it to `tag` (`seal_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO dataO lenO tlO mov ptr imm restore tagOut)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput inc32 gctr)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Spec.Gcm (ctxH)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

theorem slots_bodyFrame {D : Addr} {n : Nat} (hd : (⟨D, n⟩ : Region).Disjoint (workR W)) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W SP D n, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hd.sub_right (Lay.wSub (by decide))).symm
      · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact (L.stk_w (by decide)).symm
  · exact slots_absFrame L r hr

theorem saved_bodyFrame {D : Addr} {n : Nat} (hd : (⟨D, n⟩ : Region).Disjoint (workR W)) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W SP D n, (savedR W).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · exact saved_tFrame L (.inr rfl) r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hd.sub_right (Lay.wSub (by decide))).symm
      · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact (L.stk_w (by decide)).symm
  · exact saved_absFrame L (.inr rfl) r hr

theorem st0_bodyFrame {D : Addr} {n : Nat} (hd : (⟨D, n⟩ : Region).Disjoint (workR W)) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W SP D n, (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact st0_disj L (by decide) (by decide)
      · exact st0_w L ⟨by decide, by decide⟩
      · exact st0_w L ⟨by decide, by decide⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hd.sub_right (Lay.wSub (by decide))).symm
      · exact st0_disj L (by decide) (by decide)
      · exact (L.stk_w (by decide)).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact st0_disj L (by decide) (by decide)
    · exact st0_disj L (by decide) (by decide)
    · exact st0_w L ⟨by decide, by decide⟩

end

theorem ofNat_toNat' (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `finPrep`: the lengths from their slots. -/
theorem finPrep_ok {s : State} {W : Addr} (h19 : s.gpr .x19 = W) (hr : Covers [⟨W, 768⟩] (s.rd ++ s.wr))
    {al n : Nat} (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n) :
    WP isa (.block finPrep) s fun s' => s'.gpr .x26 = BitVec.ofNat 64 al ∧ s'.gpr .x27 = BitVec.ofNat 64 n ∧
      Regs [.x26, .x27] s s' := by
  obtain q₁ := in_off hr (show 224 + 8 ≤ 768 by decide) (by decide)
  obtain q₂ := in_off hr (show 240 + 8 ≤ 768 by decide) (by decide)
  refine WP.run ⟨_, by simp only [finPrep]; arun [h19, q₁, q₂], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
    rw [show s.mem.read (W + 224#64) 8 = s.mem.readW (W + BitVec.ofNat 64 224) 64 from rfl, sL]; rfl
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
    rw [show s.mem.read (W + 240#64) 8 = s.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl, sN]; rfl

/-- The load of the slot at `W + 248` into `x28`. -/
theorem ldr28_ok {Ctx W SP : Addr} {V : BitVec 64} {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (sT : s.mem.readW (W + BitVec.ofNat 64 248) 64 = V) :
    WP isa (.block [.ldr .x .x28 .x19 tlO]) s fun s' => s'.gpr .x28 = V ∧ Regs [.x28] s s' := by
  obtain q := he.perm.wR (show 248 + 8 ≤ 768 by decide)
  refine WP.run ⟨_, by arun [he.x19, q], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
  rw [show s.mem.read (W + 248#64) 8 = s.mem.readW (W + BitVec.ofNat 64 248) 64 from rfl, sT]; rfl

/-- `x7` kept at `W + 248` and in `x28`. -/
theorem stash7_ok {s : State} {W : Addr} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 768⟩] s.wr) :
    WP isa (.block [.str .x .x7 .x19 tlO, mov .x28 .x7]) s fun s' =>
      s'.gpr .x28 = s.gpr .x7 ∧ s'.mem = s.mem.writeW (W + BitVec.ofNat 64 248) (s.gpr .x7) ∧
      Others [.x28] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain w := in_off hw (show 248 + 8 ≤ 768 by decide) (by decide)
  refine WP.run ⟨_, by arun [h19, w], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨by simp [gpr_write], ?_, by others_tac, rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]

/-- `sealPre`'s common arguments. -/
theorem sealCore {s : State} (hs : sealPre s) : oneCore 1 0 s := by
  simp only [sealPre] at hs
  sig_split hs
  rename_i hsp hrd hwr dcd dct dcw dnd dnt dnw dad dat daw ddt ddw dda dtw dta dwa kc kn ka kd kt kw wc wn wa wd
    wt ww
  have wsp := hs
  clear hs
  exact ⟨by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp, by rw [hwr]; simp,
    by rw [hwr]; simp, dcd, dcw, dnd, dnw, dad, daw, ddw, dda, dwa, kc, kn, ka, kd, kw, wc, wn, wa, wd, ww,
    by omega_arith, hsp⟩

/-- What `sealPre` gives. -/
theorem sealLay {s : State} (hs : sealPre s) :
    OneLay s 1 0 ∧ Covers [⟨s.gpr .x7, 16⟩] s.wr ∧
      (⟨s.gpr .x7, 16⟩ : Region).Disjoint (workR (stackArg s 0)) ∧
      (⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region).Disjoint ⟨s.gpr .x7, 16⟩ := by
  have hs' := hs
  simp only [sealPre] at hs'
  obtain ⟨-, -, hwr, -, -, -, -, -, -, -, -, -, ddt, -, -, dtw, -⟩ := hs'
  exact ⟨oneLay (sealCore hs), covers_of_mem (by rw [hwr]; simp), dtw, ddt⟩

/-- What the entry of `seal` leaves, from `s`. -/
structure SealEntry (s s₁ : State) : Prop where
  env : Env (s.gpr .x0) (stackArg s 0 + BitVec.ofNat 64 16) (stackArg s 0) s.sp s₁
  x23 : s₁.gpr .x23 = s.gpr .x1
  x24 : s₁.gpr .x24 = s.gpr .x2
  x26 : s₁.gpr .x26 = s.gpr .x2
  x27 : s₁.gpr .x27 = 0
  x28 : s₁.gpr .x28 = s.gpr .x7
  sA : s₁.mem.readW (stackArg s 0 + BitVec.ofNat 64 216) 64 = s.gpr .x3
  sL : s₁.mem.readW (stackArg s 0 + BitVec.ofNat 64 224) 64 = s.gpr .x4
  sD : s₁.mem.readW (stackArg s 0 + BitVec.ofNat 64 232) 64 = s.gpr .x5
  sN : s₁.mem.readW (stackArg s 0 + BitVec.ofNat 64 240) 64 = s.gpr .x6
  sT : s₁.mem.readW (stackArg s 0 + BitVec.ofNat 64 248) 64 = s.gpr .x7
  frame : Frame [entryR (stackArg s 0)] s.mem s₁.mem
  saved : SavedAt s₁.mem (stackArg s 0) s
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

/-- The entry of `seal`. -/
theorem sealEntry_ok {s : State} (hs : sealPre s) :
    WP isa (.block (oneEntry 0 ++ ([.str .x .x7 .x19 tlO, mov .x28 .x7] : List Instr))) s (SealEntry s) := by
  obtain ⟨ol, -, -, -⟩ := sealLay hs
  have hW0 : s.mem.readW (s.sp + BitVec.ofNat 64 0) 64 = stackArg s 0 := rfl
  refine WP.block_append (WP.mono (oneEntry_ok (by decide) hW0 (ol.hsp 0 (by omega_arith)) rfl ol.perm)
    fun s₁ ⟨he₁, x23₁, x24₁, x26₁, x27₁, x7₁, sl₁, sl₂, sl₃, sl₄, f₁, sv₁, rd₁, wr₁⟩ =>
      WP.mono (stash7_ok he₁.x19 he₁.perm.w) fun s₂ ⟨x28₂, m₂, og₂, sp₂, rd₂, wr₂⟩ => ?_)
  have so (d : Nat) (hd : d + 8 ≤ 248) : s₂.mem.readW (stackArg s 0 + BitVec.ofNat 64 d) 64 =
      s₁.mem.readW (stackArg s 0 + BitVec.ofNat 64 d) 64 := by
    rw [m₂, readW_writeW_other _ _ _ (.inl hd) (by omega_arith) (by decide)]
  obtain g₂ : ∀ r ∈ [Reg.x7, .x23, .x24, .x26, .x27], s₂.gpr r = s₁.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact og₂ r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨he₁.keep (fun r hr => og₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂,
    by rw [g₂ .x23 (by simp), x23₁], by rw [g₂ .x24 (by simp), x24₁],
    by rw [g₂ .x26 (by simp), x26₁], by rw [g₂ .x27 (by simp), x27₁], by rw [x28₂, x7₁],
    by rw [so 216 (by decide), sl₁], by rw [so 224 (by decide), sl₂], by rw [so 232 (by decide), sl₃],
    by rw [so 240 (by decide), sl₄], by rw [m₂, Mem.readW_writeW_self64, x7₁], ?_, ?_, by rw [rd₂, rd₁],
    by rw [wr₂, wr₁]⟩
  · rw [m₂]; exact f₁.writeW (List.mem_singleton_self _) _ (entry_contains _ (by decide) (by decide))
  · rw [m₂]
    exact sv₁.frame (rs := [⟨stackArg s 0 + BitVec.ofNat 64 248, 8⟩])
      ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))

/-- `seal` after its entry. -/
theorem sealRest_ok (v : GcmImpl) {s s₁ : State} (hs : sealPre s) (h₁ : SealEntry s s₁) :
    WP isa (sealRest v.callees) s₁ fun s' => GprAbi s s' ∧ sealAArch64.post s s' := by
  obtain ⟨he₁, x23₁, x24₁, x26₁, x27₁, _, sl₁, sl₂, sl₃, sl₄, sl₅, f₁, sv₁, rd₁, wr₁⟩ := h₁
  obtain ⟨ol, tW, dtw, ddt⟩ := sealLay hs
  simp only [sealAArch64]
  obtain ⟨L, perm, hsp, dnW, daW, ddW, dcW, daA, dnd, dad, dcd, wn, wa, wd, kn, ka, kd, nR, aR, dW⟩ := ol
  obtain h2 := ofNat_toNat' (s.gpr .x2)
  obtain h4 := ofNat_toNat' (s.gpr .x4)
  obtain h6 := ofNat_toNat' (s.gpr .x6)
  generalize hW : stackArg s 0 = W at *
  generalize hTg : s.gpr .x7 = Tg at *
  generalize hCtx : s.gpr .x0 = Ctx at *
  generalize hNp : s.gpr .x1 = Np at *
  generalize hnl : (s.gpr .x2).toNat = nl at *
  generalize hA : s.gpr .x3 = A at *
  generalize hal : (s.gpr .x4).toNat = al at *
  generalize hD : s.gpr .x5 = D at *
  generalize hn : (s.gpr .x6).toNat = n at *
  generalize hSP : s.sp = SP at *
  obtain hnlt : n < 2 ^ 64 := hn ▸ (s.gpr .x6).isLt
  unfold sealRest
  rw [← h4] at sl₂
  rw [← h6] at sl₄
  obtain sub16 : Region.Sub ⟨W + BitVec.ofNat 64 16, 80⟩ (workR W) := Lay.wSub (by decide)
  obtain kc := keep_of_sub (entryR_work W) (dcW.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide)))
  obtain hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := blockAt_frame f₁ kc
  obtain hnon : DataOk (W + BitVec.ofNat 64 16) W s₁ Np nl :=
    ⟨by rw [rd₁, wr₁]; exact nR, hnl ▸ (s.gpr .x2).isLt, wn, dnW.sub_right sub16, dnW⟩
  obtain haad : DataOk (W + BitVec.ofNat 64 16) W s₁ A al :=
    ⟨by rw [rd₁, wr₁]; exact aR, hal ▸ (s.gpr .x4).isLt, wa, daW.sub_right sub16, daW⟩
  obtain iv₁ : bytesAt s₁.mem Np nl = bytesAt s.mem Np nl :=
    bytesAt_frame f₁ (keep_of_sub (entryR_work W) dnW) (by omega_arith)
  obtain a₁ : bytesAt s₁.mem A al = bytesAt s.mem A al :=
    bytesAt_frame f₁ (keep_of_sub (entryR_work W) daW) (by omega_arith)
  refine front_ok L v he₁ (fun _ _ => rfl : Kept s₁.gpr s₁) x23₁ (by rw [x24₁, ← h2])
    (by rw [x26₁, ← h2]) x27₁ hnon haad hH₁ sl₁ sl₂ sl₃ sl₄ fun s₂ h₂ => ?_
  rw [iv₁, a₁] at h₂
  obtain hdat₂ : DataW Ctx (W + BitVec.ofNat 64 16) W SP s₂ D n :=
    ⟨⟨covers_left (by rw [h₂.wr, wr₁]; exact dW), hnlt, wd, ddW.sub_right sub16, ddW⟩,
      by rw [h₂.wr, wr₁]; exact dW, dcd, kd⟩
  obtain hB : BodyIn Ctx (W + BitVec.ofNat 64 16) W SP s₂.gpr n 0 D (bytesAt s.mem A al) [] (ctxH s.mem Ctx) s₂ :=
    ⟨h₂.env, fun _ _ => rfl, h₂.x25, h₂.x26, h₂.x27, h₂.x28, rfl, by decide, hdat₂, h₂.hH⟩
  refine WP.seq (WP.mono (WP.with_rdwr (encBody_ok L v hB (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx)
    (bytesAt s.mem Np nl))))) fun s₃ ⟨h₃, rd₃, wr₃⟩ => ?_)
  obtain ⟨o₁, o₂, o₃⟩ := h₃.post h₂.abs (Proof.Gcm.ctr_zero _ _ _ _ h₂.cb)
  obtain slot₃ : ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂' => by
    rw [slot_kept h₃.frame (slots_bodyFrame L ddW) h₁ h₂', slot_kept h₂.frame (slots_frontFrame L) h₁ h₂']
  refine WP.seq (WP.mono (finPrep_ok (al := al) (n := n) h₃.env.x19 (covers_left h₃.env.perm.w)
    (by rw [slot₃ 224 (by decide) (by decide), sl₂]) (by rw [slot₃ 240 (by decide) (by decide), sl₄]))
    fun s₄ ⟨x26₄, x27₄, r₄⟩ => ?_)
  obtain he₄ := h₃.env.of_regs r₄
  refine WP.seq (WP.mono (ldr28_ok (V := Tg) he₄ (by rw [r₄.mem, slot₃ 248 (by decide) (by decide), sl₅]))
    fun s₄' ⟨x28₄', r₄'⟩ => ?_)
  obtain he₄' := he₄.of_regs r₄'
  obtain x26₄' : s₄'.gpr .x26 = BitVec.ofNat 64 al := by rw [r₄'.others _ (by decide), x26₄]
  obtain x27₄' : s₄'.gpr .x27 = BitVec.ofNat 64 n := by rw [r₄'.others _ (by decide), x27₄]
  obtain m₄ : s₄'.mem = s₃.mem := by rw [r₄'.mem, r₄.mem]
  obtain kcd : ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W SP D n, (⟨Ctx, 256⟩ : Region).Disjoint r :=
    keep_body dcW dcd L.kc.symm
  obtain hc₃ : ciphOf s₃.mem Ctx = ciphOf s.mem Ctx := by
    rw [ciph_frame h₃.frame kcd, ciph_frame h₂.frame (keep_of_sub (frontFrame_work W) dcW),
      ciph_frame f₁ (keep_of_sub (entryR_work W) dcW)]
  obtain hD₂ : bytesAt s₂.mem D n = bytesAt s.mem D n := by
    rw [bytesAt_frame h₂.frame (keep_of_sub (frontFrame_work W) ddW) (by omega_arith),
      bytesAt_frame f₁ (keep_of_sub (entryR_work W) ddW) (by omega_arith)]
  obtain hc₂ : ciphOf s₂.mem Ctx = ciphOf s.mem Ctx := by
    rw [ciph_frame h₂.frame (keep_of_sub (frontFrame_work W) dcW),
      ciph_frame f₁ (keep_of_sub (entryR_work W) dcW)]
  obtain hH₄ : blockAt s₄'.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [m₄, blockAt_frame h₃.frame fun r hr => (kcd r hr).sub_left (Lay.ctxSub (by decide)), h₂.hH]
  obtain hlen : ([] ++ xorKs (ciphOf s₂.mem Ctx) (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) 0
      (bytesAt s₂.mem D n)).length = n := by
    rw [List.nil_append, Proof.Gcm.length_xorKs, length_bytesAt]
  refine WP.seq (WP.mono (WP.with_rdwr (finBody_ok L v (.inl rfl) (a := bytesAt s.mem A al) (H := ctxH s.mem Ctx)
    (c := [] ++ xorKs (ciphOf s₂.mem Ctx) (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) 0
      (bytesAt s₂.mem D n))
    he₄' (fun _ _ => rfl) (by rw [x26₄', length_bytesAt]) (by rw [x27₄', hlen]) (by rw [hlen]; exact hnlt)
    hH₄)) fun s₅ ⟨⟨he₅, hk₅, f₅, out₅⟩, _, wr₅⟩ => ?_)
  obtain sv₅ : SavedAt s₅.mem W s := by
    have := (sv₁.frame h₂.frame (saved_frontFrame L)).frame h₃.frame (saved_bodyFrame L ddW)
    rw [← m₄] at this
    exact this.frame f₅ (saved_finFrame L (.inl rfl))
  obtain x28₅ : s₅.gpr .x28 = Tg := by rw [hk₅ .x28 (by decide), x28₄']
  obtain wr₅' : s₅.wr = s.wr := by rw [wr₅, r₄'.wr, r₄.wr, wr₃, h₂.wr, wr₁]
  refine WP.seq (WP.mono (tagOut_ok he₅.x19 x28₅ (covers_left he₅.perm.w) (by rw [wr₅']; exact tW)
    (dtw.sub_right (Region.sub_prefix (by decide)))) fun s₆ ⟨out₆, f₆, og₆, sp₆, rd₆, wr₆⟩ => ?_)
  obtain he₆ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₆ := he₅.keep (fun r hr => og₆ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₆ rd₆ wr₆
  obtain sv₆ : SavedAt s₆.mem W s := sv₅.frame f₆ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (dtw.sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (exit_ok he₆.x19 (by rw [he₆.sp, hSP]) (covers_left he₆.perm.w) sv₆)
    fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  rw [hm]
  obtain hdata : bytesAt s₆.mem D n = gctr (ctxCiph s.mem Ctx)
      (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) (bytesAt s.mem D n) := by
    rw [bytesAt_frame f₆ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ddt) (by omega_arith),
      bytesAt_frame f₅ (keep_fin (.inl rfl) ddW kd.symm) (by omega_arith), m₄, o₃, hc₂, hD₂,
      Proof.Gcm.gctr_eq]
    rfl
  obtain hj₄ : blockAt s₄'.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl) := by
    rw [m₄, blockAt_frame h₃.frame (st0_bodyFrame L ddW), h₂.j0]
  obtain htag := out₅ (by rw [m₄]; exact o₁)
  rw [add_ofNat_zero, m₄, hc₃, ← m₄, hj₄] at htag
  obtain he : [] ++ xorKs (ciphOf s₂.mem Ctx) (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) 0
      (bytesAt s₂.mem D n) = gctr (ctxCiph s.mem Ctx)
        (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) (bytesAt s.mem D n) := by
    rw [List.nil_append, hc₂, hD₂, Proof.Gcm.gctr_eq]; rfl
  rw [he] at htag
  rw [hdata, out₆, htag, Spec.Gcm.encryptWith, Proof.Gcm.fullTag_eq,
    List.take_of_length_le (by rw [Proof.Cmac.toBytes_length])]
  rfl

theorem seal_wp (v : GcmImpl) {s : State} (hs : sealAArch64.pre s) :
    WP isa («seal» v.callees) s fun s' => GprAbi s s' ∧ sealAArch64.post s s' :=
  WP.seq (WP.mono (sealEntry_ok hs) fun _ h₁ => sealRest_ok v hs h₁)

end VG.Proof.Sm4Gcm.AArch64

end

end

/-!
# SM4-GCM on AArch64: `vg_sm4_gcm_open`

Untrusted: everything here is checked by Lean. The entry also keeps
`tag_len` at `W + 248`; if `tagLenOk` does not allow it, `open` returns 0.
Otherwise `tagIn` copies the received tag to `W`, `front_ok` starts the
state and absorbs the additional data,
`decAbs` absorbs the ciphertext, `finBody 112` writes the tag at `W + 112`,
`cmpSeg` compares it with the received one without a branch, and the data is
decrypted only if they are equal (`open_wp`), which is the one secret the
code branches on, as the contract allows.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (dataO lenO tlO mov imm restore tagIn tagLenOk cmp uO textArgs fo)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput inc32 gctr zeros)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Spec.Gcm (ctxH)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- `decAbs`: the additional data padded if this is the first text, and the
text absorbed. -/
theorem decAbs_ok (v : GcmImpl) {k : Reg → BitVec 64} {n P : Nat} {D : Addr} {a c : List Byte} {H : Block}
    {s : State} (h : BodyIn Ctx St W SP k n P D a c H s) :
    WP isa (decAbs v.callees) s fun s₄ => Env Ctx St W SP s₄ ∧ Kept k s₄ ∧
      s₄.gpr .x25 = BitVec.ofNat 64 (P % 16) ∧ Frame (tFrame St W 16 ++ absFrame St W 16) s.mem s₄.mem ∧
      s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) →
        Absorbed s₄.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
          (ghashInput a (c ++ bytesAt s.mem D n))) := by
  have k26 : k .x26 = BitVec.ofNat 64 n := (h.kept .x26 (by decide)).symm.trans h.x26
  have k27 : k .x27 = BitVec.ofNat 64 P := (h.kept .x27 (by decide)).symm.trans h.x27
  have k28 : k .x28 = D := (h.kept .x28 (by decide)).symm.trans h.x28
  have hlt := h.data.ok.lt
  refine WP.seq_assoc (WP.seq (WP.mono (pad_ok L v h) fun s₂ ⟨he₂, hk₂, hH₂, f₂, rd₂, wr₂, abs₂⟩ => ?_))
  refine WP.seq (WP.mono (textArgs_ok hk₂ k26 k27 k28 h.hP) fun s₃ ⟨x25₃, x23₃, x24₃, r₃⟩ => ?_)
  have he₃ := he₂.of_regs r₃
  have hk₃ := hk₂.of_others r₃.others
  have m₃ : s₃.mem = s₂.mem := r₃.mem
  have hD₃ : bytesAt s₃.mem D n = bytesAt s.mem D n := by
    rw [m₃]; exact bytesAt_frame f₂ (data_tFrame h.data) (by omega_arith)
  have hd₃ : DataW Ctx St W SP s₃ D n := h.data.of_eq (by rw [r₃.rd, rd₂]) (by rw [r₃.wr, wr₂])
  have F₃ : Frame (tFrame St W 16 ++ absFrame St W 16) s.mem s₃.mem := by
    rw [m₃]; exact f₂.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
  refine WP.ite (decide (n = 0)) (eval_zero ((hk₃ .x26 (by decide)).trans k26) hlt) (fun ht => ?_) (fun hf => ?_)
  · have hn0 : n = 0 := by simpa using ht
    refine WP.block_nil ⟨he₃, hk₃, x25₃, F₃, by rw [r₃.rd, rd₂], by rw [r₃.wr, wr₂], fun ha => ?_⟩
    rw [ghashInput_xf, length_bytesAt, hn0, show bytesAt s.mem D 0 = [] from rfl, List.append_nil, m₃]
    have := abs₂ ha
    rw [hn0] at this
    exact this
  · have hn0 : n ≠ 0 := by simpa using hf
    have hA : AbsIn Ctx St W SP k H (xf a c n) D n (P % 16) s₃ :=
      ⟨he₃, hk₃, x23₃, x24₃, x25₃, by rw [xf_len hn0, h.hc], hd₃.ok, by rw [m₃, hH₂]⟩
    refine WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) v hA)) fun s₄ ⟨h₄, rd₄, wr₄⟩ =>
      ⟨h₄.env, h₄.kept, h₄.x25,
        F₃.trans (h₄.frame.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩),
        by rw [rd₄, r₃.rd, rd₂], by rw [wr₄, r₃.wr, wr₂], fun ha => ?_⟩
    rw [ghashInput_xf, length_bytesAt, ← hD₃]
    exact h₄.abs (by rw [m₃]; exact abs₂ ha)

end

end VG.Proof.Sm4Gcm.AArch64

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (dataO lenO tlO mov imm restore tagIn tagLenOk cmp uO textArgs fo)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput inc32 gctr zeros)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Spec.Gcm (ctxH)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- The regions `openMain` writes, but the data. -/
abbrev omFrame (W SP : Addr) : List Region :=
  frontFrame (W + BitVec.ofNat 64 16) W ++ (tFrame (W + BitVec.ofNat 64 16) W 16 ++
    absFrame (W + BitVec.ofNat 64 16) W 16) ++ finFrame (W + BitVec.ofNat 64 16) W SP 112 ++
    [⟨W + BitVec.ofNat 64 256, 32⟩]

theorem omFrame_work (W SP : Addr) : ∀ r ∈ omFrame W SP, Region.Sub r (workR W) ∨ r = stk SP := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  rotate_left
  · simp only [List.mem_singleton] at hr; subst hr; exact .inl (Lay.wSub (by decide))
  rcases List.mem_append.mp hr with hr | hr
  rotate_left
  · exact finFrame_work W SP (.inr rfl) r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact .inl (frontFrame_work W r hr)
  rcases List.mem_append.mp hr with hr | hr
  · exact .inl ((bodyFrame_work W SP 0 0 r (mem_bt hr)).resolve_right (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp))
  · exact .inl ((bodyFrame_work W SP 0 0 r (mem_ba hr)).resolve_right (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp))

theorem keep_om {W SP : Addr} {X : Region} (hX : X.Disjoint (workR W)) (hS : X.Disjoint (stk SP)) :
    ∀ r ∈ omFrame W SP, X.Disjoint r := fun r hr => by
  rcases omFrame_work W SP r hr with h | rfl
  · exact hX.sub_right h
  · exact hS

theorem saved_omFrame {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) :
    ∀ r ∈ omFrame W SP, (savedR W).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  rotate_left
  · exact saved_cmp L r hr
  rcases List.mem_append.mp hr with hr | hr
  rotate_left
  · exact saved_finFrame L (.inr rfl) r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact saved_frontFrame L r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact saved_tFrame L (.inr rfl) r hr
  · exact saved_absFrame L (.inr rfl) r hr

/-- What `openMain` writes is above the received tag, or the callee's stack. -/
theorem omFrame_hi (W SP : Addr) :
    ∀ r ∈ omFrame W SP, Region.Sub r ⟨W + BitVec.ofNat 64 16, 752⟩ ∨ r = stk SP := by
  have hi : ∀ d k, 16 ≤ d → d + k ≤ 768 →
      Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ ⟨W + BitVec.ofNat 64 16, 752⟩ :=
    fun d k h₁ h₂ => Offset.sub _ h₁ (by omega_arith)
  have st : ∀ d k, d + k ≤ 80 →
      Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ ⟨W + BitVec.ofNat 64 16, 752⟩ :=
    fun d k h => Offset.sub_base _ (by omega_arith)
  have st0 : ∀ k, k ≤ 80 → Region.Sub ⟨W + BitVec.ofNat 64 16, k⟩ ⟨W + BitVec.ofNat 64 16, 752⟩ :=
    fun k h => Region.sub_prefix (by omega_arith)
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  rotate_left
  · simp only [List.mem_singleton] at hr; subst hr; exact .inl (hi _ _ (by decide) (by decide))
  rcases List.mem_append.mp hr with hr | hr
  rotate_left
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [tFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inl (st _ _ (by decide))
      · exact .inl (hi _ _ (by decide) (by decide))
      · exact .inl (hi _ _ (by decide) (by decide))
    · simp only [tagFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | h
      · exact .inl (st0 _ (by decide))
      · exact .inl (hi _ _ (by decide) (by decide))
      · exact .inl (hi _ _ (by decide) (by decide))
      · exact .inl (hi _ _ (by decide) (by decide))
      · exact .inr h
  refine .inl ?_
  rcases List.mem_append.mp hr with hr | hr
  · simp only [frontFrame, j0Frame, absFrame, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact st0 _ (by decide)
    · exact hi _ _ (by decide) (by decide)
    · exact hi _ _ (by decide) (by decide)
    · exact st _ _ (by decide)
    · exact st _ _ (by decide)
    · exact hi _ _ (by decide) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · simp only [tFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact st _ _ (by decide)
    · exact hi _ _ (by decide) (by decide)
    · exact hi _ _ (by decide) (by decide)
  · simp only [absFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact st _ _ (by decide)
    · exact st _ _ (by decide)
    · exact hi _ _ (by decide) (by decide)

/-- The tag compared: 1 in `x27` if it is right, 0 if not. -/
theorem okBit_ok {s : State} {b : Bool} (h10 : s.gpr .x10 = BitVec.ofNat 64 (if b then 0 else 1)) :
    WP isa (.block [imm .x27 1, .sub .x .x27 .x27 .x10]) s fun s' =>
      s'.gpr .x27 = BitVec.ofNat 64 (if b then 1 else 0) ∧ Regs [.x27] s s' := by
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h10]
  cases b <;> decide

/-- `openMain` up to the branch on the tag. -/
def omA (c : Callees) : Prog isa :=
  .seq (j0 c) (.seq (oneAad c) (.seq (.block encPrep) (.seq (decAbs c) (.seq (.block finPrep)
    (.seq (finBody c uO) (.seq (.block [.ldr .x .x28 .x19 tlO]) (.seq cmp
      (.block [imm .x27 1, .sub .x .x27 .x27 .x10]))))))))

/-- The rest: the branch on the tag, and the result. -/
def omB (c : Callees) : Prog isa :=
  .seq (.ite (.zero .x .x27) (.block []) (oneCrypt c)) (.block [mov .x0 .x27])

theorem Exec.seq_assoc {a b c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa (.seq a (.seq b c)) s t s') :
    Exec isa (.seq (.seq a b) c) s t s' := by
  cases h with
  | seq e₁ e₂ => cases e₂ with
    | seq eb ec => rw [← List.append_assoc]; exact .seq (.seq e₁ eb) ec

theorem Exec.seq_assoc' {a b c : Prog isa} {s s' : State} {t : List Leak}
    (h : Exec isa (.seq (.seq a b) c) s t s') : Exec isa (.seq a (.seq b c)) s t s' := by
  cases h with
  | seq e₁ e₂ => cases e₁ with
    | seq ea eb => rw [List.append_assoc]; exact .seq ea (.seq eb e₂)

/-- Programs with the same runs. -/
def PEq (c₁ c₂ : Prog isa) : Prop := ∀ s t s', Exec isa c₁ s t s' ↔ Exec isa c₂ s t s'

theorem PEq.assoc (a b c : Prog isa) : PEq (.seq (.seq a b) c) (.seq a (.seq b c)) :=
  fun _ _ _ => ⟨Exec.seq_assoc', Exec.seq_assoc⟩

theorem PEq.seq_right (a : Prog isa) {b b' : Prog isa} (h : PEq b b') : PEq (.seq a b) (.seq a b') := by
  intro s t s'
  constructor
  · intro e; cases e with | seq e₁ e₂ => exact .seq e₁ ((h _ _ _).mp e₂)
  · intro e; cases e with | seq e₁ e₂ => exact .seq e₁ ((h _ _ _).mpr e₂)

theorem PEq.symm {a b : Prog isa} (h : PEq a b) : PEq b a := fun s t s' => (h s t s').symm

theorem PEq.trans {a b c : Prog isa} (h₁ : PEq a b) (h₂ : PEq b c) : PEq a c :=
  fun s t s' => (h₁ s t s').trans (h₂ s t s')

theorem PEq.wp {a b : Prog isa} (h : PEq a b) {s : State} {Q : State → Prop} (w : WP isa b s Q) : WP isa a s Q := by
  obtain ⟨t, s', e, q⟩ := w; exact ⟨t, s', (h _ _ _).mpr e, q⟩

theorem PEq.rel {a b : Prog isa} (h : PEq a b) {P Q : State → State → Prop} (r : RelCT isa P b Q) :
    RelCT isa P a Q := fun _ _ _ _ _ _ hp e₁ e₂ => r _ _ _ _ _ _ hp ((h _ _ _).mp e₁) ((h _ _ _).mp e₂)

/-- `openMain` is `omA` then `omB`. -/
theorem openMain_split (c : Callees) : PEq (.seq (omA c) (omB c)) (openMain c) := by
  unfold omA omB openMain
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  exact PEq.assoc _ _ _

/-- What is known at the branch of `openMain`, memory having changed since
`s` only in `fr`. -/
structure MidO (fr : List Region) (Ctx W SP D Np A : Addr) (nl al n tl : Nat) (s s₇ : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s₇
  frame : Frame fr s.mem s₇.mem
  x27 : s₇.gpr .x27 = BitVec.ofNat 64 (if decide ((Spec.Gcm.fullTag (ciphOf s.mem Ctx)
    (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl) (bytesAt s.mem A al)
    (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl) then 1 else 0)
  data : DataW Ctx (W + BitVec.ofNat 64 16) W SP s₇ D n
  sD : s₇.mem.readW (W + BitVec.ofNat 64 232) 64 = D
  sN : s₇.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n
  cb : blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
    inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl))

/-- The slots are outside what `openMain` writes before the branch. -/
theorem slots_omFrame {Ctx W SP D : Addr} {n : Nat} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
    (ddW : (⟨D, n⟩ : Region).Disjoint (workR W)) :
    ∀ r ∈ omFrame W SP, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  rotate_left
  · simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  rotate_left
  · rcases List.mem_append.mp hr with hr | hr
    · exact slots_bodyFrame L ddW r (mem_bt hr)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · simpa using (L.st_w (a := 0) (n := 32) (d := 216) (k := 40) (by decide)
          (.inr ⟨by decide, by decide⟩)).symm
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w (by decide)).symm
  rcases List.mem_append.mp hr with hr | hr
  · exact slots_frontFrame L r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact slots_bodyFrame L ddW r (mem_bt hr)
  · exact slots_bodyFrame L ddW r (mem_ba hr)

theorem openMainA_ok (v : GcmImpl) {Ctx W SP D Np A : Addr} {nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (h23 : s.gpr .x23 = Np) (h24 : s.gpr .x24 = BitVec.ofNat 64 nl)
    (h26 : s.gpr .x26 = BitVec.ofNat 64 nl) (h27 : s.gpr .x27 = 0)
    (hnon : DataOk (W + BitVec.ofNat 64 16) W s Np nl) (haad : DataOk (W + BitVec.ofNat 64 16) W s A al)
    (hdat : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n) (ddW : (⟨D, n⟩ : Region).Disjoint (workR W))
    (dcW : (⟨Ctx, 256⟩ : Region).Disjoint (workR W))
    (sA : s.mem.readW (W + BitVec.ofNat 64 216) 64 = A)
    (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (sD : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D)
    (sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n)
    (sT : s.mem.readW (W + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 tl)
    (hok : Spec.Gcm.tagLenOk tl = true) :
    WP isa (omA v.callees) s (MidO (omFrame W SP) Ctx W SP D Np A nl al n tl s) := by
  unfold omA
  have hle := tagLenOk_le hok
  have hnlt := hdat.ok.lt
  have dD : ∀ r ∈ omFrame W SP, (⟨D, n⟩ : Region).Disjoint r := keep_om ddW hdat.stk.symm
  have dC : ∀ r ∈ omFrame W SP, (⟨Ctx, 256⟩ : Region).Disjoint r := keep_om dcW L.kc.symm
  have sl := slots_omFrame L ddW
  have mF : ∀ {rs : List Region}, (∀ r ∈ rs, r ∈ omFrame W SP) → ∀ {m m' : Mem}, Frame rs m m' →
      Frame (omFrame W SP) m m' := fun hs _ _ hf => hf.mono hs
  refine front_ok L v he (fun _ _ => rfl : Kept s.gpr s) h23 h24 h26 h27 hnon haad rfl sA sL sD sN
    fun s₁ h₁ => ?_
  have F₁ : Frame (omFrame W SP) s.mem s₁.mem :=
    mF (fun r hr => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hr))) h₁.frame
  have hdat₁ : DataW Ctx (W + BitVec.ofNat 64 16) W SP s₁ D n := hdat.of_eq h₁.rd h₁.wr
  have hB : BodyIn Ctx (W + BitVec.ofNat 64 16) W SP s₁.gpr n 0 D (bytesAt s.mem A al) []
      (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) s₁ :=
    ⟨h₁.env, fun _ _ => rfl, h₁.x25, h₁.x26, h₁.x27, h₁.x28, rfl, by decide, hdat₁,
      h₁.hH⟩
  refine WP.seq (WP.mono (decAbs_ok L v hB) fun s₂ ⟨he₂, hk₂, x25₂, f₂, rd₂, wr₂, abs₂⟩ => ?_)
  have F₂ : Frame (omFrame W SP) s.mem s₂.mem :=
    F₁.trans (mF (fun r hr => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hr))) f₂)
  have slot : ∀ {m : Mem}, Frame (omFrame W SP) s.mem m → ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      m.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun hf d h₁ h₂ => slot_kept hf sl h₁ h₂
  refine WP.seq (WP.mono (finPrep_ok (al := al) (n := n) he₂.x19 (covers_left he₂.perm.w) (by rw [slot F₂ 224 (by decide) (by decide), sL])
    (by rw [slot F₂ 240 (by decide) (by decide), sN])) fun s₃ ⟨x26₃, x27₃, r₃⟩ => ?_)
  have he₃ := he₂.of_regs r₃
  have F₃ : Frame (omFrame W SP) s.mem s₃.mem := by rw [r₃.mem]; exact F₂
  have hC₁ : bytesAt s₁.mem D n = bytesAt s.mem D n := bytesAt_frame F₁ dD (by omega_arith)
  have hlen : ([] ++ bytesAt s₁.mem D n).length = n := by rw [List.nil_append, length_bytesAt]
  have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = blockAt s.mem (Ctx + BitVec.ofNat 64 240) :=
    blockAt_frame F₃ fun r hr => (dC r hr).sub_left (Lay.ctxSub (by decide))
  refine WP.seq (WP.mono (WP.with_rdwr (finBody_ok L v (.inr rfl) (a := bytesAt s.mem A al)
    (c := [] ++ bytesAt s₁.mem D n)
    (H := blockAt s.mem (Ctx + BitVec.ofNat 64 240)) he₃ (fun _ _ => rfl)
    (by rw [x26₃, length_bytesAt]) (by rw [x27₃, hlen]) (by rw [hlen]; exact hnlt) hH₃))
    fun s₄ ⟨⟨he₄, hk₄, f₄, out₄⟩, rd₄, wr₄⟩ => ?_)
  have F₄ : Frame (omFrame W SP) s.mem s₄.mem :=
    F₃.trans (mF (fun r hr => List.mem_append_left _ (List.mem_append_right _ hr)) f₄)
  obtain ⟨s₅, run₅, x28₅, r₅⟩ : ∃ s₅, runBlock isa [.ldr .x .x28 .x19 tlO] s₄ = some s₅ ∧
      s₅.gpr .x28 = BitVec.ofNat 64 tl ∧ Regs [.x28] s₄ s₅ := by
    have q := he₄.perm.wR (show 248 + 8 ≤ 768 by decide)
    have e := slot F₄ 248 (by decide) (by decide)
    rw [sT] at e
    refine ⟨_, by arun [he₄.x19, q], ?_⟩
    refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
    rw [show s₄.mem.read (W + 248#64) 8 = s₄.mem.readW (W + BitVec.ofNat 64 248) 64 from rfl, e]; rfl
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := he₄.of_regs r₅
  refine WP.seq (WP.mono (WP.with_rdwr (cmp_ok L he₅ (fun _ _ => rfl : Kept s₅.gpr s₅) x28₅ hle))
    fun s₆ ⟨⟨x10₆, he₆, hk₆, _, f₆⟩, rd₆, wr₆⟩ => ?_)
  refine WP.mono (okBit_ok (b := decide (bytesAt s₅.mem (W + BitVec.ofNat 64 112) tl =
      bytesAt s₅.mem W tl)) (by rw [x10₆]; simp only [decide_eq_true_eq]))
    fun s₇ ⟨x27₇, r₇⟩ => ?_
  have he₇ := he₆.of_regs r₇
  have F₇ : Frame (omFrame W SP) s.mem s₇.mem := by
    rw [r₇.mem]
    exact F₄.trans (by rw [← r₅.mem]; exact mF (fun r hr => List.mem_append_right _ hr) f₆)
  -- The tag and the comparison.
  have hab : Absorbed s₃.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32)
      (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (ghashInput (bytesAt s.mem A al) ([] ++ bytesAt s₁.mem D n)) := by
    rw [r₃.mem]; exact abs₂ h₁.abs
  have hj₃ : blockAt s₃.mem (W + BitVec.ofNat 64 16) =
      Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl) := by
    rw [r₃.mem, blockAt_frame f₂ (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact st0_bodyFrame L ddW r (mem_bt hr)
      · exact st0_bodyFrame L ddW r (mem_ba hr)), h₁.j0]
  have hT₅ : bytesAt s₅.mem (W + BitVec.ofNat 64 112) 16 = Spec.Gcm.fullTag (ciphOf s.mem Ctx)
      (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n) := by
    rw [r₅.mem, out₄ hab, ciph_frame F₃ dC, hj₃, Proof.Gcm.fullTag_eq, List.nil_append, hC₁]
  have hW₅ : bytesAt s₅.mem W tl = bytesAt s.mem W tl := by
    rw [r₅.mem]
    refine bytesAt_frame F₄ (fun r hr => ?_) (by omega_arith)
    rcases omFrame_hi W SP r hr with h | rfl
    · have := (Offset.disjoint W (d := 0) (n := tl) (e := 16) (k := 752) (.inl (by omega_arith)) (by omega_arith)
        (by decide)).sub_right h
      simpa using this
    · simpa using (L.stk_w (a := 0) (n := tl) (by omega_arith)).symm
  have hb : (bytesAt s₅.mem (W + BitVec.ofNat 64 112) tl = bytesAt s₅.mem W tl) ↔
      (Spec.Gcm.fullTag (ciphOf s.mem Ctx) (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl)
        (bytesAt s.mem A al) (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl := by
    rw [← bytesAt_take _ _ hle, hT₅, hW₅]
  generalize hBd : decide (bytesAt s₅.mem (W + BitVec.ofNat 64 112) tl = bytesAt s₅.mem W tl) = B at x27₇
  have hBeq : decide ((Spec.Gcm.fullTag (ciphOf s.mem Ctx) (blockAt s.mem (Ctx + BitVec.ofNat 64 240))
      (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl) = B := by
    rw [← hBd]; exact decide_eq_decide.mpr hb.symm
  have hD₇ : bytesAt s₇.mem D n = bytesAt s.mem D n := bytesAt_frame F₇ dD (by omega_arith)
  have hcb : blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
      inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl)) := by
    have d₁ : ∀ r ∈ tFrame (W + BitVec.ofNat 64 16) W 16 ++ absFrame (W + BitVec.ofNat 64 16) W 16,
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact (acc_tFrame_free L r hr).sub_left (Region.sub_prefix (by decide))
      · exact (ctr_absFrame L r hr).sub_left (Region.sub_prefix (by decide))
    have d₂ : ∀ r ∈ finFrame (W + BitVec.ofNat 64 16) W SP 112,
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact (acc_tFrame_free L r hr).sub_left (Region.sub_prefix (by decide))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · simpa using L.st_st (a := 48) (n := 16) (d := 0) (k := 32) (.inr (by decide)) (by decide) (by decide)
        · exact st_wpart L (by decide) ⟨by decide, by decide⟩
        · exact st_wpart L (by decide) ⟨by decide, by decide⟩
        · exact st_wpart L (by decide) ⟨by decide, by decide⟩
        · exact (L.stk_st (by decide)).symm
    have d₃ : ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 32⟩ : Region)],
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact st_wpart L (by decide) ⟨by decide, by decide⟩
    rw [r₇.mem, blockAt_frame f₆ d₃, r₅.mem, blockAt_frame f₄ d₂, r₃.mem, blockAt_frame f₂ d₁, h₁.cb]
  exact ⟨he₇, F₇, by rw [x27₇, hBeq],
    hdat.of_eq (by rw [r₇.rd, rd₆, r₅.rd, rd₄, r₃.rd, rd₂, h₁.rd]) (by rw [r₇.wr, wr₆, r₅.wr, wr₄, r₃.wr, wr₂, h₁.wr]),
    by rw [slot F₇ 232 (by decide) (by decide), sD], by rw [slot F₇ 240 (by decide) (by decide), sN], hcb⟩

/-- The loads before `crypt` in `oneCrypt`. -/
theorem ocLdr_ok {Ctx W SP D : Addr} {n : Nat} {s₇ : State} (he₇ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₇)
    (sD₇ : s₇.mem.readW (W + BitVec.ofNat 64 232) 64 = D)
    (sN₇ : s₇.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n) :
    WP isa (.block [.ldr .x .x23 .x19 dataO, .ldr .x .x24 .x19 lenO, imm .x25 0]) s₇ fun s₈ =>
      s₈.gpr .x23 = D ∧ s₈.gpr .x24 = BitVec.ofNat 64 n ∧
        s₈.gpr .x25 = BitVec.ofNat 64 (0 % 16) ∧ Regs [.x23, .x24, .x25] s₇ s₈ := by
  have q₁ := he₇.perm.wR (show 232 + 8 ≤ 768 by decide)
  have q₂ := he₇.perm.wR (show 240 + 8 ≤ 768 by decide)
  refine WP.run ⟨_, by arun [he₇.x19, q₁, q₂], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ?_, by simp [gpr_write], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
    rw [show s₇.mem.read (W + 232#64) 8 = s₇.mem.readW (W + BitVec.ofNat 64 232) 64 from rfl, sD₇]; rfl
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
    rw [show s₇.mem.read (W + 240#64) 8 = s₇.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl, sN₇]; rfl

/-- What `crypt` needs in `oneCrypt`, after its loads. -/
theorem oc_in {Ctx W SP D Np A : Addr} {nl al n tl : Nat}
    {fr : List Region} {s s₇ s₈ : State}
    (mo : MidO fr Ctx W SP D Np A nl al n tl s s₇)
    (h : s₈.gpr .x23 = D ∧ s₈.gpr .x24 = BitVec.ofNat 64 n ∧
        s₈.gpr .x25 = BitVec.ofNat 64 (0 % 16) ∧ Regs [.x23, .x24, .x25] s₇ s₈) :
    CrIn Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr 0 D n s₈ :=
  ⟨mo.env.of_regs h.2.2.2, fun _ _ => rfl, h.1, h.2.1, h.2.2.1,
    mo.data.of_eq h.2.2.2.rd h.2.2.2.wr⟩

theorem omIte_ok (v : GcmImpl) {Ctx W SP D Np A : Addr} {nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) {fr : List Region} {s s₇ : State}
    (mo : MidO fr Ctx W SP D Np A nl al n tl s s₇) (dD : ∀ r ∈ fr, (⟨D, n⟩ : Region).Disjoint r)
    (dC : ∀ r ∈ fr, (⟨Ctx, 256⟩ : Region).Disjoint r) :
    WP isa (.ite (.zero .x .x27) (.block []) (oneCrypt v.callees)) s₇ fun s₈ =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₈ ∧ s₈.gpr .x27 = s₇.gpr .x27 ∧
      Frame (crFrame (W + BitVec.ofNat 64 16) SP D n) s₇.mem s₈.mem ∧
      bytesAt s₈.mem D n = if decide ((Spec.Gcm.fullTag (ciphOf s.mem Ctx)
          (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl) (bytesAt s.mem A al)
          (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl) then
        gctr (ciphOf s.mem Ctx) (inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240))
          (bytesAt s.mem Np nl))) (bytesAt s.mem D n) else bytesAt s.mem D n := by
  have hnlt := mo.data.ok.lt
  have F₇ := mo.frame
  have hD₇ : bytesAt s₇.mem D n = bytesAt s.mem D n := bytesAt_frame F₇ dD (by omega_arith)
  have x27₇ := mo.x27
  generalize decide ((Spec.Gcm.fullTag (ciphOf s.mem Ctx) (blockAt s.mem (Ctx + BitVec.ofNat 64 240))
    (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl) = B at x27₇ ⊢
  refine WP.ite (decide ((if B then 1 else 0) = 0)) (eval_zero x27₇ (by cases B <;> decide)) (fun ht => ?_)
    (fun hf => ?_)
  · have hB : B = false := by revert ht; cases B <;> simp
    subst hB
    exact WP.block_nil ⟨mo.env, rfl, Frame.refl _ _, by rw [hD₇]; rfl⟩
  · have hB : B = true := by revert hf; cases B <;> simp
    subst hB
    refine WP.seq (WP.mono (ocLdr_ok mo.env mo.sD mo.sN) fun s₈ h₈ => ?_)
    have r₈ := h₈.2.2.2
    have F₈ : Frame fr s.mem s₈.mem := by rw [r₈.mem]; exact F₇
    have hcb₈ : blockAt s₈.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
        inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl)) := by
      rw [r₈.mem, mo.cb]
    have hc₈ : ciphOf s₈.mem Ctx = ciphOf s.mem Ctx := ciph_frame F₈ dC
    have hD₈ : bytesAt s₈.mem D n = bytesAt s.mem D n := bytesAt_frame F₈ dD (by omega_arith)
    refine WP.mono (cryptAl_ok L v (oc_in mo h₈) rfl
      (icb := inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl))))
      fun s₉ h₉ => ⟨h₉.env, ?_, by rw [← r₈.mem]; exact h₉.frame, ?_⟩
    · rw [h₉.kept .x27 (by decide), r₈.others _ (by decide)]
    · rw [h₉.out (Proof.Gcm.ctr_zero _ _ _ _ hcb₈), hc₈, hD₈, Proof.Gcm.gctr_eq]
      rfl

theorem omB_ok (v : GcmImpl) {Ctx W SP D Np A : Addr} {nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) {fr : List Region} {s s₇ : State}
    (mo : MidO fr Ctx W SP D Np A nl al n tl s s₇) (dD : ∀ r ∈ fr, (⟨D, n⟩ : Region).Disjoint r)
    (dC : ∀ r ∈ fr, (⟨Ctx, 256⟩ : Region).Disjoint r) :
    WP isa (omB v.callees) s₇ fun s' =>
      let ciph := ciphOf s.mem Ctx
      let H := blockAt s.mem (Ctx + BitVec.ofNat 64 240)
      let T := Spec.Gcm.fullTag ciph H (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)
      let b := decide (T.take tl = bytesAt s.mem W tl)
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ Frame (⟨D, n⟩ :: fr ++ crFrame (W + BitVec.ofNat 64 16) SP D n) s.mem s'.mem ∧
      s'.gpr .x0 = BitVec.ofNat 64 (if b then 1 else 0) ∧
      bytesAt s'.mem D n = if b then gctr ciph (inc32 (Spec.Gcm.j0 H (bytesAt s.mem Np nl))) (bytesAt s.mem D n)
        else bytesAt s.mem D n := by
  unfold omB
  refine WP.seq (WP.mono (omIte_ok v L mo dD dC) fun s₈ ⟨he₈, x27₈, f₈, d₈⟩ => ?_)
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨he₈.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl, ?_, by simp [gpr_write, x27₈, mo.x27], d₈⟩
  exact (mo.frame.sub fun r hr => ⟨r, List.mem_cons_of_mem _ (List.mem_append_left _ hr), fun _ h => h⟩).trans
    (f₈.sub fun r hr => ⟨r, List.mem_cons_of_mem _ (List.mem_append_right _ hr), fun _ h => h⟩)

theorem openMain_ok (v : GcmImpl) {Ctx W SP D Np A : Addr} {nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (h23 : s.gpr .x23 = Np) (h24 : s.gpr .x24 = BitVec.ofNat 64 nl)
    (h26 : s.gpr .x26 = BitVec.ofNat 64 nl) (h27 : s.gpr .x27 = 0)
    (hnon : DataOk (W + BitVec.ofNat 64 16) W s Np nl) (haad : DataOk (W + BitVec.ofNat 64 16) W s A al)
    (hdat : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n) (ddW : (⟨D, n⟩ : Region).Disjoint (workR W))
    (dcW : (⟨Ctx, 256⟩ : Region).Disjoint (workR W))
    (sA : s.mem.readW (W + BitVec.ofNat 64 216) 64 = A)
    (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (sD : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D)
    (sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n)
    (sT : s.mem.readW (W + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 tl)
    (hok : Spec.Gcm.tagLenOk tl = true) :
    WP isa (openMain v.callees) s fun s' =>
      let ciph := ciphOf s.mem Ctx
      let H := blockAt s.mem (Ctx + BitVec.ofNat 64 240)
      let T := Spec.Gcm.fullTag ciph H (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)
      let b := decide (T.take tl = bytesAt s.mem W tl)
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ Frame (⟨D, n⟩ :: omFrame W SP ++ crFrame (W + BitVec.ofNat 64 16) SP D n) s.mem s'.mem ∧
      s'.gpr .x0 = BitVec.ofNat 64 (if b then 1 else 0) ∧
      bytesAt s'.mem D n = if b then gctr ciph (inc32 (Spec.Gcm.j0 H (bytesAt s.mem Np nl))) (bytesAt s.mem D n)
        else bytesAt s.mem D n :=
  (openMain_split v.callees).symm.wp (WP.seq (c₁ := omA v.callees) (WP.mono (openMainA_ok v L he h23 h24 h26 h27 hnon haad hdat ddW dcW
    sA sL sD sN sT hok) fun _ mo => omB_ok v L mo (keep_om ddW hdat.stk.symm) (keep_om dcW L.kc.symm)))

end VG.Proof.Sm4Gcm.AArch64

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (dataO lenO tlO mov imm restore tagIn tagLenOk cmp uO textArgs fo)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput inc32 gctr zeros)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Spec.Gcm (ctxH)

/-- What is known after `open`'s entry, from the state `s₀` it was called in, with the
received tag the `tl` bytes at `Tg`. -/
structure OpenIn (Ctx W SP Np A D Tg : Addr) (nl al n tl : Nat) (s₀ s : State) : Prop where
  lay : Lay Ctx (W + BitVec.ofNat 64 16) W SP
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  x23 : s.gpr .x23 = Np
  x24 : s.gpr .x24 = BitVec.ofNat 64 nl
  x26 : s.gpr .x26 = BitVec.ofNat 64 nl
  x27 : s.gpr .x27 = 0
  x28 : s.gpr .x28 = BitVec.ofNat 64 tl
  tlt : tl < 2 ^ 64
  non : DataOk (W + BitVec.ofNat 64 16) W s Np nl
  aad : DataOk (W + BitVec.ofNat 64 16) W s A al
  dat : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n
  tagR : Covers [⟨Tg, tl⟩] (s.rd ++ s.wr)
  dnW : (⟨Np, nl⟩ : Region).Disjoint (workR W)
  daW : (⟨A, al⟩ : Region).Disjoint (workR W)
  ddW : (⟨D, n⟩ : Region).Disjoint (workR W)
  dcW : (⟨Ctx, 256⟩ : Region).Disjoint (workR W)
  dtW : (⟨Tg, tl⟩ : Region).Disjoint (workR W)
  sA : s.mem.readW (W + BitVec.ofNat 64 216) 64 = A
  sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al
  sD : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D
  sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n
  sT : s.mem.readW (W + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 tl
  fr : Frame [entryR W, ⟨W, 16⟩] s₀.mem s.mem
  sv : SavedAt s.mem W s₀
  sp₀ : s₀.sp = SP
  rd₀ : s.rd = s₀.rd
  wr₀ : s.wr = s₀.wr

theorem OpenIn.of_regs {Ctx W SP Np A D Tg : Addr} {nl al n tl : Nat} {s₀ s s' : State}
    (o : OpenIn Ctx W SP Np A D Tg nl al n tl s₀ s) (r : Regs [.x9, .x10] s s') :
    OpenIn Ctx W SP Np A D Tg nl al n tl s₀ s' :=
  ⟨o.lay, o.env.of_regs r, by rw [r.others _ (by decide), o.x23],
    by rw [r.others _ (by decide), o.x24], by rw [r.others _ (by decide), o.x26],
    by rw [r.others _ (by decide), o.x27], by rw [r.others _ (by decide), o.x28], o.tlt,
    o.non.of_eq r.rd r.wr, o.aad.of_eq r.rd r.wr, o.dat.of_eq r.rd r.wr, by rw [r.rd, r.wr]; exact o.tagR,
    o.dnW, o.daW, o.ddW, o.dcW, o.dtW,
    by rw [r.mem, o.sA], by rw [r.mem, o.sL], by rw [r.mem, o.sD], by rw [r.mem, o.sN], by rw [r.mem, o.sT],
    by rw [r.mem]; exact o.fr, by rw [r.mem]; exact o.sv, o.sp₀, r.rd.trans o.rd₀, r.wr.trans o.wr₀⟩

/-- What the entry and `tagIn` write is in `work`. -/
theorem entry16_work (W : Addr) : ∀ r ∈ [entryR W, ⟨W, 16⟩], Region.Sub r (workR W) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Lay.wSub (by decide)
  · exact Region.sub_prefix (by decide)

/-- `OpenIn` after `tagIn`. -/
theorem OpenIn.tagIn {Ctx W SP Np A D Tg : Addr} {nl al n tl : Nat} {s₀ s s' : State}
    (o : OpenIn Ctx W SP Np A D Tg nl al n tl s₀ s) (f : Frame [⟨W, 16⟩] s.mem s'.mem)
    (og : Others loopRegs s s') (sp : s'.sp = s.sp) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) :
    OpenIn Ctx W SP Np A D Tg nl al n tl s₀ s' := by
  have L := o.lay
  have sl : ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    slot_kept f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using L.w_w (a := 216) (n := 40) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)) h₁ h₂
  exact ⟨L, o.env.keep (fun r hr => og r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp rd wr,
    by rw [og _ (by decide), o.x23],
    by rw [og _ (by decide), o.x24], by rw [og _ (by decide), o.x26],
    by rw [og _ (by decide), o.x27], by rw [og _ (by decide), o.x28], o.tlt,
    o.non.of_eq rd wr, o.aad.of_eq rd wr, o.dat.of_eq rd wr, by rw [rd, wr]; exact o.tagR,
    o.dnW, o.daW, o.ddW, o.dcW, o.dtW,
    by rw [sl 216 (by decide) (by decide), o.sA], by rw [sl 224 (by decide) (by decide), o.sL],
    by rw [sl 232 (by decide) (by decide), o.sD], by rw [sl 240 (by decide) (by decide), o.sN],
    by rw [sl 248 (by decide) (by decide), o.sT],
    o.fr.trans (f.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩),
    o.sv.frame f (saved_tag16 L), o.sp₀, rd.trans o.rd₀, wr.trans o.wr₀⟩

/-- `openPre`'s common arguments. -/
theorem openCore {s : State} (hs : openPre s) : oneCore 2 1 s := by
  simp only [openPre] at hs
  sig_split hs
  rename_i hsp hrd hwr dcd dcw dnd dnw dad daw dtd ddw dda dtw dwa kc kn ka kd kt kw wc wn wa wd wt ww
  have wsp := hs
  clear hs
  exact ⟨by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp, by rw [hwr]; simp,
    by rw [hwr]; simp, dcd, dcw, dnd, dnw, dad, daw, ddw, dda, dwa, kc, kn, ka, kd, kw, wc, wn, wa, wd, ww,
    wsp, hsp⟩

/-- What `openPre` gives. -/
theorem openLay {s : State} (hs : openPre s) :
    OneLay s 2 1 ∧ Covers [⟨s.gpr .x7, (stackArg s 0).toNat⟩] (s.rd ++ s.wr) ∧
      (⟨s.gpr .x7, (stackArg s 0).toNat⟩ : Region).Disjoint (workR (stackArg s 1)) := by
  have hs' := hs
  simp only [openPre] at hs'
  obtain ⟨-, hrd, hwr, -, -, -, -, -, -, -, -, -, dtw, -⟩ := hs'
  exact ⟨oneLay (openCore hs), covers_mem (by rw [hrd, hwr]; simp), dtw⟩

/-- `tag_len` (at `sp`) kept at `W + 248` and in `x28`, and `tag` in `x12`. -/
theorem openStash_ok {s : State} {W : Addr} {V : BitVec 64} (h19 : s.gpr .x19 = W)
    (hw : Covers [⟨W, 768⟩] s.wr) (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 0) 8)
    (hV : s.mem.readW (s.sp + BitVec.ofNat 64 0) 64 = V) :
    WP isa (.block [.ldrSp .x10 0, .str .x .x10 .x19 tlO, mov .x28 .x10, mov .x12 .x7]) s fun s' =>
      s'.gpr .x28 = V ∧ s'.gpr .x12 = s.gpr .x7 ∧ s'.mem = s.mem.writeW (W + BitVec.ofNat 64 248) V ∧
      Others [.x10, .x28, .x12] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w := in_off hw (show 248 + 8 ≤ 768 by decide) (by decide)
  refine WP.run ⟨_, by arun [h19, hsp, w], rfl⟩ fun s' hs' => ?_
  subst hs'
  have e : s.mem.read s.sp 8 = V := by rw [← hV, BitVec.add_zero]; rfl
  refine ⟨by simp [gpr_write, e], by simp [gpr_write], ?_, by others_tac, rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
  rw [BitVec.add_zero, e]

/-- `open`'s first block: the entry, the tag length and the tag. -/
theorem openEntry_ok {s : State} (hs : openPre s) :
    WP isa (.block openEntry) s fun s' =>
      OpenIn (s.gpr .x0) (stackArg s 1) s.sp (s.gpr .x1) (s.gpr .x3) (s.gpr .x5) (s.gpr .x7)
        (s.gpr .x2).toNat (s.gpr .x4).toNat (s.gpr .x6).toNat (stackArg s 0).toNat s s' ∧
      s'.gpr .x12 = s.gpr .x7 := by
  obtain ⟨ol, tR, dtW⟩ := openLay hs
  obtain ⟨L, perm, hsp, dnW, daW, ddW, dcW, daA, dnd, dad, dcd, wn, wa, wd, kn, ka, kd, nR, aR, dW⟩ := ol
  have hW8 : s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = stackArg s 1 := rfl
  have hT0 : s.mem.readW (s.sp + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (stackArg s 0).toNat := by
    rw [ofNat_toNat']; rfl
  have hsp8 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 := hsp 1 (by omega_arith)
  have hsp0 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 0) 8 := hsp 0 (by omega_arith)
  have darg0 : (⟨s.sp + BitVec.ofNat 64 0, 8⟩ : Region).Disjoint (workR (stackArg s 1)) := by
    refine daA.sub_left ?_
    show Region.Sub ⟨s.sp + BitVec.ofNat 64 0, 8⟩ ⟨s.sp + BitVec.ofNat 64 (8 * 0), 8 * 2⟩
    exact Region.sub_prefix (by omega_arith)
  have h2 := ofNat_toNat' (s.gpr .x2)
  have h4 := ofNat_toNat' (s.gpr .x4)
  have h6 := ofNat_toNat' (s.gpr .x6)
  unfold openEntry
  refine WP.block_append (WP.mono (oneEntry_ok (k := 8) (by decide) hW8 hsp8 rfl perm)
    fun s₁ ⟨he₁, x23₁, x24₁, x26₁, x27₁, x7₁, sl₁, sl₂, sl₃, sl₄, f₁, sv₁, rd₁, wr₁⟩ =>
      WP.mono (openStash_ok (V := BitVec.ofNat 64 (stackArg s 0).toNat) he₁.x19 he₁.perm.w
        (by rw [rd₁, wr₁, he₁.sp]; exact hsp0)
        (by rw [he₁.sp, f₁.readW (r := ⟨s.sp + BitVec.ofNat 64 0, 8⟩) (Region.contains_self _ _)
          (keep_of_sub (entryR_work _) darg0) (by decide), hT0]))
      fun s₂ ⟨x28₂, x12₂, m₂, og₂, sp₂, rd₂, wr₂⟩ => ?_)
  refine ⟨?_, by rw [x12₂, x7₁]⟩
  generalize hW : stackArg s 1 = W at *
  generalize hCtx : s.gpr .x0 = Ctx at *
  generalize hNp : s.gpr .x1 = Np at *
  generalize hnl : (s.gpr .x2).toNat = nl at *
  generalize hA : s.gpr .x3 = A at *
  generalize hal : (s.gpr .x4).toNat = al at *
  generalize hD : s.gpr .x5 = D at *
  generalize hn : (s.gpr .x6).toNat = n at *
  generalize htlv : (stackArg s 0).toNat = tl at *
  have hnlt : n < 2 ^ 64 := hn ▸ (s.gpr .x6).isLt
  have htlt : tl < 2 ^ 64 := htlv ▸ (stackArg s 0).isLt
  rw [← h4] at sl₂
  rw [← h6] at sl₄
  have so (d : Nat) (hd : d + 8 ≤ 248) : s₂.mem.readW (W + BitVec.ofNat 64 d) 64 =
      s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    rw [m₂, readW_writeW_other _ _ _ (.inl hd) (by omega_arith) (by decide)]
  have sub16 : Region.Sub ⟨W + BitVec.ofNat 64 16, 80⟩ (workR W) := Lay.wSub (by decide)
  have g : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x26, .x27], s₂.gpr r = s₁.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact og₂ r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have rd₄ : s₂.rd = s.rd := by rw [rd₂, rd₁]
  have wr₄ : s₂.wr = s.wr := by rw [wr₂, wr₁]
  refine ⟨L, he₁.keep (fun r hr => g r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp)) sp₂ rd₂ wr₂,
    by rw [g .x23 (by simp), x23₁], by rw [g .x24 (by simp), x24₁, ← h2], by rw [g .x26 (by simp), x26₁, ← h2],
    by rw [g .x27 (by simp), x27₁], x28₂, htlt,
    ⟨by rw [rd₄, wr₄]; exact nR, hnl ▸ (s.gpr .x2).isLt, wn, dnW.sub_right sub16, dnW⟩,
    ⟨by rw [rd₄, wr₄]; exact aR, hal ▸ (s.gpr .x4).isLt, wa, daW.sub_right sub16, daW⟩,
    ⟨⟨covers_left (by rw [wr₄]; exact dW), hnlt, wd, ddW.sub_right sub16, ddW⟩, by rw [wr₄]; exact dW, dcd, kd⟩,
    by rw [rd₄, wr₄]; exact tR, dnW, daW, ddW, dcW, dtW,
    by rw [so 216 (by decide), sl₁], by rw [so 224 (by decide), sl₂],
    by rw [so 232 (by decide), sl₃], by rw [so 240 (by decide), sl₄], by rw [m₂, Mem.readW_writeW_self64],
    ?_, ?_, rfl, rd₄, wr₄⟩
  · rw [m₂]
    exact (f₁.writeW (List.mem_singleton_self _) _ (entry_contains W (by decide) (by decide))).sub
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩
  · rw [m₂]
    exact sv₁.frame (rs := [⟨W + BitVec.ofNat 64 248, 8⟩])
      ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide))

/-- What `openMain` reads, in a state after `tagIn`, as it was on entry. -/
theorem OpenIn.vals {Ctx W SP Np A D Tg : Addr} {nl al n tl : Nat} {s₀ t : State}
    (o : OpenIn Ctx W SP Np A D Tg nl al n tl s₀ t) :
    ciphOf t.mem Ctx = ctxCiph s₀.mem Ctx ∧ blockAt t.mem (Ctx + BitVec.ofNat 64 240) = ctxH s₀.mem Ctx ∧
      bytesAt t.mem Np nl = bytesAt s₀.mem Np nl ∧ bytesAt t.mem A al = bytesAt s₀.mem A al ∧
      bytesAt t.mem D n = bytesAt s₀.mem D n := by
  have hnlt := o.dat.ok.lt
  have hnl := o.non.lt
  have hal := o.aad.lt
  have kE : ∀ {X : Region}, X.Disjoint (workR W) → ∀ r ∈ [entryR W, ⟨W, 16⟩], X.Disjoint r :=
    fun hX => keep_of_sub (entry16_work W) hX
  exact ⟨ciph_frame o.fr (kE o.dcW), blockAt_frame o.fr (kE (o.dcW.sub_left (Lay.ctxSub (by decide)))),
    bytesAt_frame o.fr (kE o.dnW) (by omega_arith), bytesAt_frame o.fr (kE o.daW) (by omega_arith),
    bytesAt_frame o.fr (kE o.ddW) (by omega_arith)⟩

/-- The received tag, after `tagIn`, as it was on entry. -/
theorem OpenIn.tag {Ctx W SP Np A D Tg : Addr} {nl al n tl : Nat} {s₀ s : State}
    (o : OpenIn Ctx W SP Np A D Tg nl al n tl s₀ s) : bytesAt s.mem Tg tl = bytesAt s₀.mem Tg tl :=
  bytesAt_frame o.fr (keep_of_sub (entry16_work W) o.dtW) (by have := o.tlt; omega_arith)

/-- What `open` leaves after its branch on the tag length, from the state
`s₀` it was called in. -/
abbrev OpenPost (Ctx W SP Np A D Tg : Addr) (nl al n tl : Nat) (s₀ s₄ : State) : Prop :=
  Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ ∧ SavedAt s₄.mem W s₀ ∧
    match Spec.Gcm.openResult (ctxCiph s₀.mem Ctx) (ctxH s₀.mem Ctx) tl (bytesAt s₀.mem Np nl)
        (bytesAt s₀.mem D n) (bytesAt s₀.mem A al) (bytesAt s₀.mem Tg tl) with
    | some pt => (s₄.gpr .x0).setWidth 32 = 1 ∧ bytesAt s₄.mem D n = pt
    | none => (s₄.gpr .x0).setWidth 32 = 0 ∧ bytesAt s₄.mem D n = bytesAt s₀.mem D n

/-- `openMain`, once the received tag is at `W`. -/
theorem openMain_post (v : GcmImpl) {Ctx W SP Np A D Tg : Addr} {nl al n tl : Nat} {s₀ t : State}
    (o' : OpenIn Ctx W SP Np A D Tg nl al n tl s₀ t) (hT₃ : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl)
    (hok : Spec.Gcm.tagLenOk tl = true) :
    WP isa (openMain v.callees) t (OpenPost Ctx W SP Np A D Tg nl al n tl s₀) := by
  have L := o'.lay
  refine WP.mono (openMain_ok v L o'.env  o'.x23 o'.x24 o'.x26 o'.x27 o'.non o'.aad o'.dat
    o'.ddW o'.dcW o'.sA o'.sL o'.sD o'.sN o'.sT hok) fun s₄ hpost => ?_
  dsimp only at hpost
  obtain ⟨he₄, F₄, x0₄, d₄⟩ := hpost
  refine ⟨he₄, o'.sv.frame F₄ fun r hr => ?_, ?_⟩
  · rcases List.mem_cons.mp hr with h | hr
    · subst h; exact (o'.ddW.sub_right (Lay.wSub (by decide))).symm
    rcases List.mem_append.mp hr with hr | hr
    · exact saved_omFrame L r hr
    · exact saved_crFrame L o'.dat r hr
  · obtain ⟨hc₃, hH₃, hN₃, hA₃, hD₃⟩ := o'.vals
    rw [hc₃, hH₃, hN₃, hA₃, hD₃, hT₃] at x0₄ d₄
    rw [Spec.Gcm.openResult, ite_eq_left hok, Spec.Gcm.decryptWith]
    by_cases hc : (Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)
        (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)).take tl = bytesAt s₀.mem Tg tl
    · rw [ite_eq_left hc]
      simp only [hc, decide_true, ite_true] at x0₄ d₄
      exact ⟨by rw [x0₄]; rfl, d₄⟩
    · rw [ite_eq_right hc]
      simp only [hc, decide_false, Bool.false_eq_true, ite_false] at x0₄ d₄
      exact ⟨by rw [x0₄]; rfl, d₄⟩

/-- `open`'s branch on the tag length, with `m` once the received tag is at `W`. -/
theorem oiteWith_ok {m : Prog isa} {Ctx W SP Np A D Tg : Addr} {nl al n tl : Nat} {s₀ s₃ : State}
    (o : OpenIn Ctx W SP Np A D Tg nl al n tl s₀ s₃) (x12₃ : s₃.gpr .x12 = Tg)
    (x9₃ : s₃.gpr .x9 = BitVec.ofNat 64 (if Spec.Gcm.tagLenOk tl then 1 else 0))
    (hm : ∀ {t : State}, OpenIn Ctx W SP Np A D Tg nl al n tl s₀ t →
      bytesAt t.mem W tl = bytesAt s₀.mem Tg tl → Spec.Gcm.tagLenOk tl = true →
      Others loopRegs s₃ t →
      WP isa m t (OpenPost Ctx W SP Np A D Tg nl al n tl s₀)) :
    WP isa (.ite (.zero .x .x9) (.block [imm .x0 0]) (.seq tagIn m)) s₃
      (OpenPost Ctx W SP Np A D Tg nl al n tl s₀) := by
  have ev : isa.eval (.zero .x .x9) s₃ = some (decide ((if Spec.Gcm.tagLenOk tl then 1 else 0) = 0)) :=
    eval_zero x9₃ (by split <;> decide)
  refine WP.ite _ ev (fun ht => ?_) (fun hf => ?_)
  · have hok : Spec.Gcm.tagLenOk tl = false := by
      revert ht; cases Spec.Gcm.tagLenOk tl <;> simp
    refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
    subst hs'
    refine ⟨o.env.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl, o.sv, ?_⟩
    rw [Spec.Gcm.openResult, ite_eq_right (by simp [hok])]
    exact ⟨by simp [gpr_write], o.vals.2.2.2.2⟩
  · have hok : Spec.Gcm.tagLenOk tl = true := by
      revert hf; cases Spec.Gcm.tagLenOk tl <;> simp
    have hle := tagLenOk_le hok
    refine WP.seq (WP.mono (tagIn_ok o.env.x19 x12₃ o.x28 hle o.tagR o.env.perm.w
      (o.dtW.sub_right (Region.sub_prefix (by decide)))) fun s₃' ⟨rt, f, og, sp, rd, wr⟩ => ?_)
    exact hm (o.tagIn f og sp rd wr) (by rw [rt, o.tag]) hok og

/-- `open` after its entry, with `m` once the received tag is at `W`, from
the registers `x4` to `x7` of the entry. -/
theorem openRestWith_wp {m : Prog isa} {s s₂ : State}
    (o₂ : OpenIn (s.gpr .x0) (stackArg s 1) s.sp (s.gpr .x1) (s.gpr .x3) (s.gpr .x5) (s.gpr .x7)
      (s.gpr .x2).toNat (s.gpr .x4).toNat (s.gpr .x6).toNat (stackArg s 0).toNat s s₂)
    (x12₂ : s₂.gpr .x12 = s.gpr .x7)
    (hm : ∀ {t : State}, OpenIn (s.gpr .x0) (stackArg s 1) s.sp (s.gpr .x1) (s.gpr .x3) (s.gpr .x5) (s.gpr .x7)
        (s.gpr .x2).toNat (s.gpr .x4).toNat (s.gpr .x6).toNat (stackArg s 0).toNat s t →
      bytesAt t.mem (stackArg s 1) (stackArg s 0).toNat = bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat →
      Spec.Gcm.tagLenOk (stackArg s 0).toNat = true →
      WP isa m t (OpenPost (s.gpr .x0) (stackArg s 1) s.sp (s.gpr .x1) (s.gpr .x3) (s.gpr .x5) (s.gpr .x7)
        (s.gpr .x2).toNat (s.gpr .x4).toNat (s.gpr .x6).toNat (stackArg s 0).toNat s)) :
    WP isa (.seq tagLenOk (.seq (.ite (.zero .x .x9) (.block [imm .x0 0]) (.seq tagIn m)) (.block restore))) s₂
      fun s' => GprAbi s s' ∧ openAArch64.post s s' := by
  refine WP.seq (WP.mono (tagLenOk_ok s₂ o₂.x28 o₂.tlt) fun s₃ ⟨x9₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (oiteWith_ok (o₂.of_regs r₃) (by rw [r₃.others _ (by decide), x12₂]) x9₃
    fun o' hT hok _ => hm o' hT hok) fun s₄ ⟨he₄, sv₄, post₄⟩ => ?_)
  refine WP.mono (exit_ok he₄.x19 (he₄.sp.trans o₂.sp₀.symm) (covers_left he₄.perm.w) sv₄)
    fun s' ⟨ga, hm, hx0, _⟩ => ⟨ga, ?_⟩
  simp only [openAArch64, openRes]
  rw [hm, hx0]
  exact post₄

theorem open_wp (v : GcmImpl) {s : State} (hs : openAArch64.pre s) :
    WP isa («open» v.callees) s fun s' => GprAbi s s' ∧ openAArch64.post s s' := by
  refine WP.seq (WP.mono (openEntry_ok hs) fun s₂ ⟨o₂, x12₂⟩ => ?_)
  exact openRestWith_wp o₂ x12₂ fun o' hT hok => openMain_post v o' hT hok

end VG.Proof.Sm4Gcm.AArch64

end

end

/-!
# SM4-GCM on AArch64: `vg_sm4_gcm_stream_encrypt` and `_decrypt` are constant time

Untrusted: everything here is checked by Lean. The entry and the exit by the
taint analysis; the bodies by `encBody_rel` and `decBody_rel`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- `decAbs` in two runs. -/
theorem decAbs_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {n P : Nat} {D : Addr} {a₁ a₂ c₁ c₂ : List Byte}
    {H₁ H₂ : Block} {σ₁ σ₂ : State} (h₁ : BodyIn Ctx St W SP k₁ n P D a₁ c₁ H₁ σ₁)
    (h₂ : BodyIn Ctx St W SP k₂ n P D a₂ c₂ H₂ σ₂) (hq : a₁.length % 16 = a₂.length % 16) :
    RelCT isa (Eq2 σ₁ σ₂) (decAbs v.callees) TT := by
  have k26₁ : k₁ .x26 = BitVec.ofNat 64 n := (h₁.kept .x26 (by decide)).symm.trans h₁.x26
  have k26₂ : k₂ .x26 = BitVec.ofNat 64 n := (h₂.kept .x26 (by decide)).symm.trans h₂.x26
  exact padArgs_rel L v h₁ h₂ hq fun τ₁ τ₂ c₁ c₂ =>
    textAbs_rel L v c₁.env c₂.env c₁.kept c₂.kept c₁.x23 c₂.x23 c₁.x24 c₂.x24 c₁.x25 c₂.x25
      ((c₁.kept .x26 (by decide)).trans k26₁) ((c₂.kept .x26 (by decide)).trans k26₂) c₁.data.ok c₂.data.ok

/-- `decBody` in two runs. -/
theorem decBody_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {n P : Nat} {D : Addr} {a₁ a₂ c₁ c₂ : List Byte}
    {H₁ H₂ : Block} {σ₁ σ₂ : State} (h₁ : BodyIn Ctx St W SP k₁ n P D a₁ c₁ H₁ σ₁)
    (h₂ : BodyIn Ctx St W SP k₂ n P D a₂ c₂ H₂ σ₂) (hq : a₁.length % 16 = a₂.length % 16) :
    RelCT isa (Eq2 σ₁ σ₂) (decBody v.callees) TT := by
  have k26₁ : k₁ .x26 = BitVec.ofNat 64 n := (h₁.kept .x26 (by decide)).symm.trans h₁.x26
  have k28₁ : k₁ .x28 = D := (h₁.kept .x28 (by decide)).symm.trans h₁.x28
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
    ⟨e₁.of_regs rp₁, pk₁, p23₁, p24₁,
      by rw [rp₁.others _ (by decide), x25₁], h₁.data.of_eq (by rw [rp₁.rd, rd₁]) (by rw [rp₁.wr, wr₁])⟩
    ⟨e₂.of_regs rp₂, pk₂, p23₂, p24₂,
      by rw [rp₂.others _ (by decide), x25₂], h₂.data.of_eq (by rw [rp₂.rd, rd₂]) (by rw [rp₂.wr, wr₂])⟩

end

/-- The entry, a body and the exit, in two runs. -/
theorem cr_rel {body : Prog isa} {σ₁ σ₂ : State} (h₁ : streamCryptPre σ₁) (h₂ : streamCryptPre σ₂)
    (hq : streamCryptPub σ₁ σ₂)
    (hrel : ∀ {Ctx St W SP : Addr} {k₁ k₂ : Reg → BitVec 64} {n P : Nat} {D : Addr} {a₁ a₂ c₁ c₂ : List Byte}
      {H₁ H₂ : Block} {τ₁ τ₂ : State}, Lay Ctx St W SP → BodyIn Ctx St W SP k₁ n P D a₁ c₁ H₁ τ₁ →
      BodyIn Ctx St W SP k₂ n P D a₂ c₂ H₂ τ₂ → a₁.length % 16 = a₂.length % 16 →
      RelCT isa (Eq2 τ₁ τ₂) body TT)
    (hw : ∀ {Ctx St W SP : Addr} {k : Reg → BitVec 64} {n P : Nat} {D : Addr} {a c : List Byte} {H : Block}
      {τ : State}, Lay Ctx St W SP → BodyIn Ctx St W SP k n P D a c H τ →
      WP isa body τ fun τ' => Env Ctx St W SP τ') :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block crEntry) (.seq body (.block restore))) TT := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, qsp⟩ := hq
  simp only [streamCryptPre] at h₁ h₂
  rw [← q0, ← q1, ← q4, ← q5, ← q6, ← qsp] at h₂
  obtain ⟨hsp, hrd₁, hwr₁, dcs, dcd, dcw, dsd, dsw, ddw, sC, sS, sD, sW', wc, ws, wd, ww⟩ := h₁
  obtain ⟨-, hrd₂, hwr₂, -⟩ := h₂
  generalize hCtx : σ₁.gpr .x0 = Ctx at *
  generalize hSt : σ₁.gpr .x1 = St at *
  generalize hD : σ₁.gpr .x4 = D at *
  generalize hn : (σ₁.gpr .x5).toNat = n at *
  generalize hW : σ₁.gpr .x6 = W at *
  have L : Lay Ctx St W σ₁.sp := Lay.of wc ws ww dcs dcw dsw hsp sC sS sW'
  have hlt : n < 2 ^ 64 := hn ▸ (σ₁.gpr .x5).isLt
  have perm (σ : State) (hrd : σ.rd = [⟨Ctx, 256⟩]) (hwr : σ.wr = [⟨St, 80⟩, ⟨D, n⟩, ⟨W, 768⟩]) :
      Perm Ctx St W σ :=
    ⟨covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩
  have mk (σ σ' : State) (hwr : σ.wr = [⟨St, 80⟩, ⟨D, n⟩, ⟨W, 768⟩]) (hsd : (stk σ.sp).Disjoint ⟨D, n⟩)
      (h : Env Ctx St W σ.sp σ' ∧ Kept σ'.gpr σ' ∧
        σ'.gpr .x25 = BitVec.ofNat 64 ((σ.gpr .x2).toNat % 16) ∧ σ'.gpr .x26 = BitVec.ofNat 64 n ∧
        σ'.gpr .x27 = BitVec.ofNat 64 (σ.gpr .x3).toNat ∧ σ'.gpr .x28 = D ∧ σ'.mem = savedMem σ.mem W σ.gpr ∧
        σ'.rd = σ.rd ∧ σ'.wr = σ.wr) :
      BodyIn Ctx St W σ.sp σ'.gpr n (σ.gpr .x3).toNat D
        (Spec.Gcm.zeros ((σ.gpr .x2).toNat % 16)) (Spec.Gcm.zeros (σ.gpr .x3).toNat)
        (blockAt σ'.mem (Ctx + BitVec.ofNat 64 240)) σ' := by
    obtain ⟨he, hk, x25, x26, x27, x28, _, rd, wr⟩ := h
    exact ⟨he, hk, by rw [x25, hz_mod _ (Nat.mod_lt _ (by decide))], x26, x27, x28,
      Proof.Gcm.length_zeros _, (σ.gpr .x3).isLt,
      ⟨⟨covers_left (by rw [wr, hwr]; exact covers_of_mem (by simp)), hlt, wd, dsd.symm, ddw⟩,
        by rw [wr, hwr]; exact covers_of_mem (by simp), dcd, hsd⟩, rfl⟩
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3, .x4, .x5, .x6] qsp
      (by agree_tac [hCtx, hSt, hD, hW, ← q0, ← q1, q2, q3, ← q4, q5, ← q6]) ⟨_, by taint_decide⟩)
    (crEntry_ok hCtx hSt hD hn hW (perm σ₁ hrd₁ hwr₁))
    (crEntry_ok q0.symm q1.symm q4.symm (by rw [← q5, hn]) q6.symm (perm σ₂ hrd₂ hwr₂))
    fun τ₁ τ₂ a₁ a₂ => ?_
  have b₁ := mk σ₁ τ₁ hwr₁ sD a₁
  have b₂ := mk σ₂ τ₂ hwr₂ (by rw [← qsp]; exact sD) a₂
  rw [← qsp, ← q3] at b₂
  refine rel_seq (hrel L b₁ b₂ (by rw [Proof.Gcm.length_zeros, Proof.Gcm.length_zeros, Nat.mod_mod, Nat.mod_mod, q2]))
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

end VG.Proof.Sm4Gcm.AArch64

end

end

/-!
# SM4-GCM on AArch64: what `seal` and `open` share, in two runs

Untrusted: everything here is checked by Lean. The entry loads `work` from
the stack, which the taint analysis takes as secret (it reads memory): the
block is split after the load (`RelCT.block_split`), and the rest runs from
`x9`, which holds `work` (public) in both runs. Then `j0`, `oneAad` and
`encPrep` (`front_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

theorem RelCT.assoc' {a b c : Prog isa} {P Q : State → State → Prop}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (Exec.seq_assoc' e₁) (Exec.seq_assoc' e₂)

/-- `oneAad`'s first block. -/
theorem aadBlk_ok {s : State} {W A : Addr} {al : Nat} (h19 : s.gpr .x19 = W)
    (hr : Covers [⟨W, 768⟩] (s.rd ++ s.wr)) (sA : s.mem.readW (W + BitVec.ofNat 64 216) 64 = A)
    (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al) :
    WP isa (.block [.ldr .x .x23 .x19 aadO, .ldr .x .x24 .x19 alenO, imm .x25 0]) s fun s' =>
      s'.gpr .x23 = A ∧ s'.gpr .x24 = BitVec.ofNat 64 al ∧ s'.gpr .x25 = BitVec.ofNat 64 0 ∧
      Regs [.x23, .x24, .x25] s s' := by
  have q₁ := in_off hr (show 216 + 8 ≤ 768 by decide) (by decide)
  have q₂ := in_off hr (show 224 + 8 ≤ 768 by decide) (by decide)
  refine WP.run ⟨_, by arun [h19, q₁, q₂], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ?_, by simp [gpr_write], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; rw [← sA]; rfl
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; rw [← sL]; rfl

/-- `encPrep`. -/
theorem encPrep_ok {s : State} {W D : Addr} {al n : Nat} (h19 : s.gpr .x19 = W)
    (hr : Covers [⟨W, 768⟩] (s.rd ++ s.wr)) (hlt : al < 2 ^ 64)
    (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (sD : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D)
    (sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n) :
    WP isa (.block encPrep) s fun s' =>
      s'.gpr .x25 = BitVec.ofNat 64 (al % 16) ∧ s'.gpr .x26 = BitVec.ofNat 64 n ∧ s'.gpr .x27 = 0 ∧
      s'.gpr .x28 = D ∧ Regs [.x9, .x10, .x25, .x26, .x27, .x28] s s' := by
  have q₂ := in_off hr (show 224 + 8 ≤ 768 by decide) (by decide)
  have q₃ := in_off hr (show 232 + 8 ≤ 768 by decide) (by decide)
  have q₄ := in_off hr (show 240 + 8 ≤ 768 by decide) (by decide)
  refine WP.run ⟨_, by simp only [encPrep]; arun [h19, q₂, q₃, q₄], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ?_, by simp [gpr_write], ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    rw [show s.mem.read (W + 224#64) 8 = s.mem.readW (W + BitVec.ofNat 64 224) 64 from rfl, sL,
      show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15, toNat_ofNat_of_lt hlt]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    rw [show s.mem.read (W + 240#64) 8 = s.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl, sN]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    rw [show s.mem.read (W + 232#64) 8 = s.mem.readW (W + BitVec.ofNat 64 232) 64 from rfl, sD]

/-- What `front_ok` needs of a run. -/
structure FrontIn (Ctx St W SP : Addr) (k : Reg → BitVec 64) (Np A D : Addr) (nl al n : Nat) (s : State) :
    Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  x23 : s.gpr .x23 = Np
  x24 : s.gpr .x24 = BitVec.ofNat 64 nl
  x26 : s.gpr .x26 = BitVec.ofNat 64 nl
  x27 : s.gpr .x27 = 0
  non : DataOk St W s Np nl
  aad : DataOk St W s A al
  sA : s.mem.readW (W + BitVec.ofNat 64 216) 64 = A
  sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al
  sD : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D
  sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n

/-- What `front_rel` leaves of a run. -/
structure FrontOut (Ctx St W SP : Addr) (k : Reg → BitVec 64) (D : Addr) (al n : Nat) (s₀ s : State) :
    Prop where
  env : Env Ctx St W SP s
  x25 : s.gpr .x25 = BitVec.ofNat 64 (al % 16)
  x26 : s.gpr .x26 = BitVec.ofNat 64 n
  x27 : s.gpr .x27 = 0
  x28 : s.gpr .x28 = D
  frame : Frame (frontFrame St W) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- `j0`, `oneAad` and `encPrep` in two runs. -/
theorem front_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {Np A D : Addr} {nl al n : Nat} {σ₁ σ₂ : State}
    (h₁ : FrontIn Ctx St W SP k₁ Np A D nl al n σ₁) (h₂ : FrontIn Ctx St W SP k₂ Np A D nl al n σ₂)
    {rest : Prog isa}
    (hr : ∀ τ₁ τ₂, FrontOut Ctx St W SP k₁ D al n σ₁ τ₁ → FrontOut Ctx St W SP k₂ D al n σ₂ τ₂ →
      RelCT isa (Eq2 τ₁ τ₂) rest TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (j0 v.callees) (.seq (oneAad v.callees) (.seq (.block encPrep) rest))) TT := by
  have hlt := h₁.aad.lt
  have j₁ : J0In Ctx St W SP k₁ (blockAt σ₁.mem (Ctx + BitVec.ofNat 64 240)) Np nl σ₁ :=
    ⟨h₁.env, h₁.kept, h₁.x23, h₁.x24, h₁.x26, h₁.x27, h₁.non, rfl⟩
  have j₂ : J0In Ctx St W SP k₂ (blockAt σ₂.mem (Ctx + BitVec.ofNat 64 240)) Np nl σ₂ :=
    ⟨h₂.env, h₂.kept, h₂.x23, h₂.x24, h₂.x26, h₂.x27, h₂.non, rfl⟩
  refine rel_seq (j0_rel L v j₁ j₂) (WP.with_rdwr (j0_ok L v j₁)) (WP.with_rdwr (j0_ok L v j₂))
    fun s₁ s₂ ⟨o₁, rd₁, wr₁⟩ ⟨o₂, rd₂, wr₂⟩ => ?_
  have sl₁ := fun d (a : 216 ≤ d) (b : d + 8 ≤ 256) => slot_kept o₁.frame (slots_j0Frame L) a b
  have sl₂ := fun d (a : 216 ≤ d) (b : d + 8 ≤ 256) => slot_kept o₂.frame (slots_j0Frame L) a b
  refine RelCT.assoc' ?_
  refine rel_seq (rel_taint [.x19] (by rw [o₁.env.sp, o₂.env.sp]) (by agree_tac [o₁.env.x19, o₂.env.x19])
      ⟨_, by taint_decide⟩)
    (aadBlk_ok (A := A) (al := al) o₁.env.x19 (covers_left o₁.env.perm.w) (by rw [sl₁ 216 (by decide) (by decide), h₁.sA])
      (by rw [sl₁ 224 (by decide) (by decide), h₁.sL]))
    (aadBlk_ok (A := A) (al := al) o₂.env.x19 (covers_left o₂.env.perm.w) (by rw [sl₂ 216 (by decide) (by decide), h₂.sA])
      (by rw [sl₂ 224 (by decide) (by decide), h₂.sL]))
    fun s₁' s₂' ⟨x23₁, x24₁, x25₁, r₁⟩ ⟨x23₂, x24₂, x25₂, r₂⟩ => ?_
  have a₁ : AbsIn Ctx St W SP k₁ (blockAt s₁'.mem (Ctx + BitVec.ofNat 64 240)) [] A al 0 s₁' :=
    ⟨o₁.env.of_regs r₁, o₁.kept.of_others r₁.others, x23₁, x24₁, x25₁, rfl,
      h₁.aad.of_eq (by rw [r₁.rd, rd₁]) (by rw [r₁.wr, wr₁]), rfl⟩
  have a₂ : AbsIn Ctx St W SP k₂ (blockAt s₂'.mem (Ctx + BitVec.ofNat 64 240)) [] A al 0 s₂' :=
    ⟨o₂.env.of_regs r₂, o₂.kept.of_others r₂.others, x23₂, x24₂, x25₂, rfl,
      h₂.aad.of_eq (by rw [r₂.rd, rd₂]) (by rw [r₂.wr, wr₂]), rfl⟩
  refine rel_seq (absorbAl_rel L v (.inr rfl) a₁ a₂) (WP.with_rdwr (absorbAl_ok L (.inr rfl) v a₁))
    (WP.with_rdwr (absorbAl_ok L (.inr rfl) v a₂)) fun t₁ t₂ ⟨b₁, brd₁, bwr₁⟩ ⟨b₂, brd₂, bwr₂⟩ => ?_
  have f₁ : Frame (frontFrame St W) σ₁.mem t₁.mem :=
    (o₁.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩).trans
      (by rw [← r₁.mem]; exact b₁.frame.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩)
  have f₂ : Frame (frontFrame St W) σ₂.mem t₂.mem :=
    (o₂.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩).trans
      (by rw [← r₂.mem]; exact b₂.frame.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩)
  have tl₁ := fun d (a : 216 ≤ d) (b : d + 8 ≤ 256) => slot_kept f₁ (slots_frontFrame L) a b
  have tl₂ := fun d (a : 216 ≤ d) (b : d + 8 ≤ 256) => slot_kept f₂ (slots_frontFrame L) a b
  refine rel_seq (rel_taint [.x19] (by rw [b₁.env.sp, b₂.env.sp]) (by agree_tac [b₁.env.x19, b₂.env.x19])
      ⟨_, by taint_decide⟩)
    (encPrep_ok (D := D) (n := n) b₁.env.x19 (covers_left b₁.env.perm.w) hlt (by rw [tl₁ 224 (by decide) (by decide), h₁.sL])
      (by rw [tl₁ 232 (by decide) (by decide), h₁.sD]) (by rw [tl₁ 240 (by decide) (by decide), h₁.sN]))
    (encPrep_ok (D := D) (n := n) b₂.env.x19 (covers_left b₂.env.perm.w) hlt (by rw [tl₂ 224 (by decide) (by decide), h₂.sL])
      (by rw [tl₂ 232 (by decide) (by decide), h₂.sD]) (by rw [tl₂ 240 (by decide) (by decide), h₂.sN]))
    fun u₁ u₂ ⟨e25₁, e26₁, e27₁, e28₁, er₁⟩ ⟨e25₂, e26₂, e27₂, e28₂, er₂⟩ => ?_
  exact hr u₁ u₂ ⟨b₁.env.of_regs er₁, e25₁, e26₁, e27₁, e28₁, by rw [er₁.mem]; exact f₁,
      by rw [er₁.rd, brd₁, r₁.rd, rd₁], by rw [er₁.wr, bwr₁, r₁.wr, wr₁]⟩
    ⟨b₂.env.of_regs er₂, e25₂, e26₂, e27₂, e28₂, by rw [er₂.mem]; exact f₂,
      by rw [er₂.rd, brd₂, r₂.rd, rd₂], by rw [er₂.wr, bwr₂, r₂.wr, wr₂]⟩

end


/-- The load of `work`, at `sp + k`. -/
theorem ldr9_ok {s : State} {W : Addr} {k : Nat} (hk : k % 8 = 0 ∧ k < 32768)
    (hW : s.mem.readW (s.sp + BitVec.ofNat 64 k) 64 = W)
    (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 k) 8) :
    WP isa (.block [.ldrSp .x9 k]) s fun s' => s'.gpr .x9 = W ∧ (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  let ⟨s', run, x9, g, sp, _, rd, wr⟩ := ldrSp_ok hk hW hsp
  WP.of_runBlock ⟨s', run, x9, g, sp, rd, wr⟩

/-- The entry of `seal` and `open` in two runs, with `work` at `sp + k`. -/
theorem entry_rel {σ₁ σ₂ : State} {W : Addr} {k : Nat} (hk : k = 0 ∨ k = 8)
    (hW₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 k) 64 = W) (hW₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 k) 64 = W)
    (hsp₁ : InRegions (σ₁.rd ++ σ₁.wr) (σ₁.sp + BitVec.ofNat 64 k) 8)
    (hsp₂ : InRegions (σ₂.rd ++ σ₂.wr) (σ₂.sp + BitVec.ofNat 64 k) 8)
    (hw₁ : Covers [⟨W, 768⟩] σ₁.wr) (hw₂ : Covers [⟨W, 768⟩] σ₂.wr) (qsp : σ₁.sp = σ₂.sp)
    (hq : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (.block (oneEntry k)) TT := by
  have hk' : k % 8 = 0 ∧ k < 32768 := by rcases hk with rfl | rfl <;> decide
  have run : ∀ {σ : State}, σ.mem.readW (σ.sp + BitVec.ofNat 64 k) 64 = W →
      InRegions (σ.rd ++ σ.wr) (σ.sp + BitVec.ofNat 64 k) 8 → Covers [⟨W, 768⟩] σ.wr →
      WP isa (.block ([.ldrSp .x9 k] ++ save .x9)) σ fun s' => s'.gpr .x9 = W ∧
        (∀ r, r ≠ .x9 → s'.gpr r = σ.gpr r) ∧ s'.sp = σ.sp := fun hW hsp hw =>
    WP.block_append (WP.mono (ldr9_ok hk' hW hsp) fun s₁ ⟨x9₁, g₁, sp₁, rd₁, wr₁⟩ => by
      obtain ⟨s₂, run₂, g₂, sp₂, _, _, _⟩ := save_ok s₁ .x9 x9₁ (by rw [wr₁]; exact hw)
      exact WP.of_runBlock ⟨s₂, run₂, by rw [g₂, x9₁], fun r hr => by rw [g₂, g₁ r hr], by rw [sp₂, sp₁]⟩)
  have t₁ : ∃ h, (taint.check (Taint.ofRegs []) (.block [.ldrSp .x9 k]) h).isSome = true := by
    rcases hk with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have t₂ : ∃ h, (taint.check (Taint.ofRegs [.x9]) (.block (save .x9)) h).isSome = true := ⟨_, by taint_decide⟩
  show RelCT isa _ (.block ([.ldrSp .x9 k] ++ save .x9 ++ _)) _
  refine RelCT.block_split (rel_seq (RelCT.block_split (rel_seq (rel_taint [] qsp (by agree_tac []) t₁)
      (ldr9_ok hk' hW₁ hsp₁) (ldr9_ok hk' hW₂ hsp₂)
      fun τ₁ τ₂ ⟨x9₁, _, sp₁, _, _⟩ ⟨x9₂, _, sp₂, _, _⟩ =>
        rel_taint [.x9] (by rw [sp₁, sp₂, qsp]) (by agree_tac [x9₁, x9₂]) t₂))
    (run hW₁ hsp₁ hw₁) (run hW₂ hsp₂ hw₂) fun τ₁ τ₂ ⟨x9₁, g₁, sp₁⟩ ⟨x9₂, g₂, sp₂⟩ => ?_)
  refine rel_taint [.x9, .x0, .x1, .x2, .x3, .x4, .x5, .x6] (by rw [sp₁, sp₂, qsp]) ?_ ⟨_, by taint_decide⟩
  intro r hr
  by_cases h9 : r = .x9
  · subst h9; rw [x9₁, x9₂]
  · rw [g₁ r h9, g₂ r h9]
    exact hq r (by simp only [List.mem_cons, List.not_mem_nil, or_false, h9, false_or] at hr ⊢; exact hr)

end VG.Proof.Sm4Gcm.AArch64
