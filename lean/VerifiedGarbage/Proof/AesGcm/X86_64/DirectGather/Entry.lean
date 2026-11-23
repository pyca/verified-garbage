module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.FrontFast
public import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.First
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! Bind the gather ABI to the shared one-shot entry with the destination at stack argument two. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Impl.AesGcm.X86_64 (oneEntry)

abbrev Layout (M : CtxMode) (s : State) := GatherLayout M s 2560 2512

namespace Layout
variable {M : CtxMode} {s : State} (h : Layout M s)
include h

theorem oneCtx (hc : 256 ≤ M.len) :
    OneCtx s 6 (K s) (W s) (SP s) (Nn s) (Ad s) (Dst s) (NL s) (AL s).toNat (L s) := by
  have k : Region.Sub (below (SP s) 24) (below (SP s) 2512) := below_sub (by decide) (by decide)
  have ar : stackArgAddr s 0 = SP s + 8#64 := by simp [stackArgAddr, SP]
  apply OneCtx.ofAt (cl := M.len) (w := 5) (id := 2) (il := 3) _ hc
  · rw [h.rd]; exact covers_of_mem (r := kR M s) (by simp)
  · rw [h.rd]; exact covers_of_mem (r := nR s) (by simp)
  · rw [h.rd]; exact covers_of_mem (r := aR s) (by simp)
  · rw [h.rd]; exact covers_of_mem (r := argR s) (by simp)
  · rw [h.wr]; exact covers_of_mem (r := dR s) (by simp)
  · rw [h.wr]; exact covers_of_mem (r := ⟨W s, 2560⟩) (by simp)
  · unfold Proof.AesGcm.oneLay Proof.AesGcm.args
    rw [ar]
    exact ⟨h.k_d, h.k_w, h.n_d, h.n_w, h.a_d, h.a_w, h.d_w, h.d_a, h.w_a, h.r_d, h.r_w,
      h.b_k.sub_left k, h.b_n.sub_left k, h.b_a.sub_left k, h.b_d.sub_left k, h.b_w.sub_left k,
      h.w_k, h.w_n, h.w_ad, h.w_d, h.w_w, Nat.le_trans (by decide) h.w_sp, h.w_sp', h.rounds⟩

theorem ext : CtxExt M (K s) (W s + 16#64) (W s) (SP s) (Dst s) (L s) s := by
  refine ⟨h.w_k, h.k_w.sub_right (Lay.wSub (by decide)), h.k_w, h.k_d,
    h.b_k.sub_left (below_sub (by decide) (by decide)), ?_, h.ok⟩
  rw [h.rd]; exact covers_of_mem (r := kR M s) (by simp)

theorem front (hc : 256 ≤ M.len) : FrontRead s := by
  refine ⟨(h.oneCtx hc).args, fun hn => ?_, fun hn => ?_, ?_⟩
  · rw [h.rd]
    exact ⟨dsR s, by simp, Offset.contains_base _ (by omega) (by have := h.w_ds; omega)⟩
  · simp [fl_eq, hn, sl]
  · exact h.glen ▸ gl_mono s (k0_le s)

theorem entry_wp (hc : 256 ≤ M.len) :
    WP isa (.block (oneEntry 48 24 32)) s (OneEntry s (K s) (W s) (SP s) (Ad s) (Dst s) (L s)) := by
  have c := h.oneCtx hc
  exact WP.mono (oneEntryAt_okL (id := 2) (il := 3) (by decide) (by decide) c rfl rfl rfl rfl rfl rfl
    (c.args 5 (by decide))) fun _ e => e.1

/-- Stack arguments are preserved by nonce initialization and AAD absorption. -/
theorem stack_word {t : State}
    (fr : Frame [⟨W s, 2560⟩, below (SP s) 8] s.mem t.mem)
    (i : Nat) (hi : i < 6) :
    t.mem.readW (SP s + BitVec.ofNat 64 (8 * (i + 1))) 64 = stackArg s i := by
  have sub : Region.Sub ⟨SP s + BitVec.ofNat 64 (8 * (i + 1)), 8⟩ (argR s) := by
    rw [show 8 * (i + 1) = 8 + 8 * i by omega, ← add_ofNat_assoc]
    exact Offset.sub_base _ (by omega)
  exact fr.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.w_a.symm.sub_left sub
    · exact Offset.disjoint_below _ (by omega)) (by decide)

/-- Reading the first descriptor after the AAD phase observes its original source and length. -/
theorem first_args {t : State} (nz : 0 < Cnt s)
    (fr : Frame [⟨W s, 2560⟩, below (SP s) 8] s.mem t.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
    FirstArgs (SP s) (Src s) (Dst s) (sb s 0) (L s) (sl s 0) t := by
  have a := (h.oneCtx M.ge).args
  have covers : Covers [dsR s] (s.rd ++ s.wr) := by rw [h.rd]; exact covers_of_mem (by simp)
  have wd := h.w_ds
  have apart : ∀ r ∈ [(⟨W s, 2560⟩ : Region), below (SP s) 8], (dsR s).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.ds_w
    · exact (h.b_ds.sub_left (below_sub (by decide) (by decide))).symm
  have f₀ : (dsR s).Contains (Src s) 8 := by simpa using (Offset.contains_base (Src s) (k := Cnt s * 16) (d := 0) (n := 8) (by omega) (by decide))
  have f₁ : (dsR s).Contains (Src s + 8#64) 8 := Offset.contains_base _ (d := 8) (by omega) (by omega)
  refine ⟨h.stack_word fr 0 (by decide), h.stack_word fr 2 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [L, ofNat_toNat] using h.stack_word fr 3 (by decide)
  · rw [fr.readW f₀ apart (by decide)]; simp [sb]
  · rw [fr.readW f₁ apart (by decide)]; simp [sl]
  all_goals rw [rd, wr]
  · exact a 0 (by decide)
  · exact a 2 (by decide)
  · exact a 3 (by decide)
  · exact covers _ _ ⟨_, List.mem_singleton_self _, f₀⟩
  · exact covers _ _ ⟨_, List.mem_singleton_self _, f₁⟩

/-- The first source slice, after the AAD phase and the three public slot writes, meets
the out-of-place block-call contract. -/
theorem inputs {t : State} {H : Spec.Gcm.Block} {iv aad : List Byte} {mE : Mem}
    (m : OneMid s (K s) (W s) (SP s) (Dst s) (L s) H iv aad mE t) (nz : 0 < Cnt s) :
    Split.CallInputs M (K s) (W s) (SP s) (Dst s) (sb s 0) (s.gpr .rsi).toNat (L s) (sl s 0)
      (callState t (W s) (sb s 0) (Dst s) (L s)) := by
  have c := h.oneCtx M.ge
  have k : Region.Sub (below (SP s) 56) (below (SP s) 2512) := below_sub (by decide) (by decide)
  have region := slice_mem s (i := 0) nz
  obtain ⟨sd, -, sw⟩ := h.ls _ region
  have f := firstMem_frame t.mem (W s) (sb s 0) (Dst s) (L s)
  obtain ⟨hs, hd, _, hr⟩ := firstMem_slots t.mem (W s) (sb s 0) (Dst s) (L s)
  have ext₁ : CtxExt M (K s) (W s + 16#64) (W s) (SP s) (Dst s) (L s) t :=
    h.ext.keep m.rd m.wr m.frame (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.k_w
      · exact (h.b_k.sub_left (below_sub (by decide) (by decide))).symm)
  refine ⟨m.env.keep (fun _ _ => rfl) rfl rfl, c.lay, ⟨hr.trans m.rounds.1, m.rounds.2⟩,
    hd, hs, c.data.of_eq m.rd m.wr, ?_, sw, sd, h.w_ls _ region, ?_,
    h.b_w.sub_left k, h.b_d.sub_left k, (h.b_ls _ region).sub_left k, h.b_k.sub_left k,
    Nat.le_trans (by decide) h.w_sp, ext₁.keep rfl rfl f ?_⟩
  · change Covers [_] (t.rd ++ t.wr)
    rw [m.rd, m.wr, h.rd]; exact covers_of_mem (by simp [region])
  · have bound := h.glen ▸ gl_mono s (i := 1) nz
    simpa only [gl_succ, gl_zero, Nat.zero_add] using bound
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r; exact h.k_w

end Layout

namespace Layout
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)

variable {th : Nat} {s : State} (h : Layout (CtxMode.flaggedT th) s)
include h

theorem preparedExt (ht : 16 ≤ th) :
    CtxExt CtxMode.prepared16 (K s) (W s+16#64) (W s) (SP s) (Dst s) (L s) s := by
  have e := h.ext
  have sub : (⟨K s, 1024⟩ : Region).Sub (kR (CtxMode.flaggedT th) s) := Region.sub_prefix (show 1024 ≤ 1032 by decide)
  refine ⟨?_, e.cs.sub_left sub, e.cw.sub_left sub, e.cd.sub_left sub, e.ct.sub_right sub,
    Split.covers_pre e.cov (show 1024 ≤ 1032 by decide), e.ok.2.1 (Nat.le_trans ht e.ok.1)⟩
  have w : (K s).toNat + 1032 ≤ 2^64 := e.w
  change (K s).toNat + 1024 ≤ 2^64
  omega

abbrev Initial (s : State) := OneEntry s (K s) (W s) (SP s) (Ad s) (Dst s) (L s)
abbrev AadDone (s u : State) := OneMid s (K s) (W s) (SP s) (Dst s) (L s) (ctxH s.mem (K s))
  (bytesAt s.mem (Nn s) 12) (bytesAt s.mem (Ad s) (AL s).toNat) u.mem

theorem aad_wp (hf : Short.ShortFacts) (ht : 16 ≤ th) {u : State} (e : Initial s u)
    (hn : NL s = 12) (ha : (AL s).toNat ≤ 16) :
    WP isa VG.Impl.AesGcm.X86_64.Fast.aad u (AadDone s u) := by
  exact Fast.aad_mid hf (hn ▸ h.oneCtx (CtxMode.flaggedT th).ge) (h.preparedExt ht) e rfl hn rfl ha

abbrev WholeDone (s u m : State) (v : State) :=
  AadDone s u m ∧ Split.Mid2 (K s) (W s) (SP s) (Dst s) (sb s 0) (s.gpr .rsi).toNat (sl s 0)
    (callState m (W s) (sb s 0) (Dst s) (L s)) v

theorem aad_blocks_wp (hf : Short.ShortFacts) (T : BlkToFn (CtxMode.flaggedT th)) (ht : 16 ≤ th)
    {u : State} (e : Initial s u) (g : frontGo false s = true) :
    WP isa (.seq VG.Impl.AesGcm.X86_64.Fast.aad (VG.Impl.AesGcm.X86_64.DirectGather.firstBlocks T.fn)) u
      fun v => ∃ m, WholeDone s u m v := by
  obtain ⟨nonce, count, aad, _⟩ := front_limits (h.front (CtxMode.flaggedT th).ge) g
  have hn : NL s = 12 := by simp [NL, nonce]
  have nz : 0 < Cnt s := by omega
  refine WP.seq (WP.mono (h.aad_wp hf ht e hn aad) fun m mid => ?_)
  exact WP.mono (firstBlocks_wp T mid.env (h.first_args nz mid.frame mid.rd mid.wr) (h.inputs mid nz))
    fun v blocks => ⟨m, mid, blocks⟩

end Layout
end VG.Proof.AesGcm.X86_64.DirectGather
