module

-- separate module: it builds in parallel with the constant-time proofs that do not need it (`CTBase`,
-- `CTBlocks`).
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Pub
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Hashes
public import VerifiedGarbage.Proof.HashTable.RISCV64
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSAES-OAEP encryption on RISC-V: correctness

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Correct.lean`): the checks of the lengths (`chkK`,
`chkMsg`: `k < 2 hLen + 2` and `msg_len > k - 2 hLen - 2`, from the top bits
of differences), then either zeros and 0 (`fail_ok`) or `EM` (`em_ok`,
`mask_ok`) and RSAEP of it (`call_ok`), with MGF1's hash function the table's: if `pre` holds the
modulus' values, RSAES-OAEP-ENCRYPT (RFC 8017 §7.1.1). `code_correct`: the
function against its contract, for tables of `vs` (`tab_of`: the table is one
of them, whose hash function it names).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_sub wp_srl wp_or wp_nil eval_nonzero)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.HashTable.RISCV64 (TVar tables fnsOf Coh)

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- The result and `out`, from the entry state `s`: the octets `encrypt`
returns, or zeros. -/
def Post (Hs Gs : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ (PreOk s →
    Spec.Rsa.written s'.mem (s.gpr .a0) (kk s) ((s'.gpr .a0).setWidth 32)
      (Spec.RsaOaep.encrypt Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (kk s))
        (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) (labB s) (msgB s) (seedB Hs.len s)))

/-- Before the restores. -/
def Done (Hs Gs : Spec.Mgf1.Hash) (s t : State) : Prop :=
  Saves s t ∧ (PreOk s →
    Spec.Rsa.written t.mem (s.gpr .a0) (kk s) ((t.gpr .a0).setWidth 32)
      (Spec.RsaOaep.encrypt Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (kk s))
        (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) (labB s) (msgB s) (seedB Hs.len s)))


section
variable {H G : Hash} (hH : HashOK H) (hG : HashOK G) (fH : FitsF H) (fG : FitsF G) {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
  {f : Fns} {s : State} (P : PreO H.D s) (T : TabS G f 7 S s (stackArg s 7))
include hH hG fH fG hHh hHl hGh hGl hGv P T

omit hH hG fH fG hHh hGh hGl hGv T in
theorem fail_done {t : State} (h : Base S vO s t) (hl : kk s < 2 * H.D + 2 + mLen s) :
    WP isa encFail t (Done Hs Gs s) :=
  WP.mono (fail_ok P h) fun t' ⟨sv, h3, hb⟩ => ⟨sv, fun _ => by
    rw [Proof.RsaOaep.encrypt_none (by rw [bytesAt_length, bytesAt_length, hHl]; exact hl), h3]
    exact ⟨rfl, hb⟩⟩

theorem main_done {t : State} (E : Entered s t) (hsy : t.syms = s.syms) (hk : 2 * H.D + 2 + mLen s ≤ kk s) :
    WP isa (encMain H f) t (Done Hs Gs s) := by
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  refine em_ok P hH fH hHh rfl E hk fun t₁ b₁ y₁ he => ?_
  refine mask_ok P hG fG T hGh hGl hGv rfl hD0 hD64 (bytesAt_length _ _ _)
    (by rw [hHh, hH.hashLen]) (bytesAt_length _ _ _) hk b₁ (y₁.trans hsy) he fun t₂ b₂ hem => ?_
  refine WP.seq (WP.mono (pubArgs_ok P b₂ hem) fun t₃ a₃ => WP.mono (call_ok P a₃) fun t₄ ⟨sv, res⟩ =>
    ⟨sv, fun hc => ?_⟩)
  have hs : (seedB Hs.len s).length = Hs.len := bytesAt_length _ _ _
  rw [Proof.RsaOaep.encrypt_some hs (by rw [bytesAt_length, bytesAt_length, hHl]; exact hk), bytesAt_length,
    bytesAt_length, hHl]
  exact res hc

theorem checks_done {t : State} (E : Entered s t) (hsy : t.syms = s.syms) :
    WP isa (checks H f) t (Done Hs Gs s) := by
  have hD64 := hH.hD64
  have hk2 := P.k2
  have ek : kk s = (s.gpr .a3).toNat := rfl
  have b := E.base
  refine WP.seq (WP.of_syms (wp_li (imm := 2 * H.D + 2) (by omega) fun t₁ o₁ e₁ => wp_sub fun t₂ o₂ e₂ =>
    wp_srl fun t₃ o₃ e₃ => wp_nil fun y₃ => ?_))
  have k₃ : Only [.a0] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  have b₃ := b.only P.fits k₃
  have r0 : (t₃.gpr .a0 != 0) = decide (kk s < 2 * H.D + 2) := by
    rw [e₃, e₂, e₁, o₁.get .s1, b.s1, ← ofNat_toNat (s.gpr .a3)]
    exact ne_zero_ltBit (by omega) (by omega)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_done hHl P b₃
    (by rw [r0] at hc; simp at hc; omega)) (fun hc => ?_)
  have hk : 2 * H.D + 2 ≤ kk s := by rw [r0] at hc; simp at hc; omega
  refine WP.seq (WP.of_syms (wp_li (imm := 2 * H.D + 2) (by omega) fun t₄ o₄ e₄ => wp_sub fun t₅ o₅ e₅ =>
    wp_sub fun t₆ o₆ e₆ => wp_srl fun t₇ o₇ e₇ => wp_srl fun t₈ o₈ e₈ => wp_or fun t₉ o₉ e₉ =>
      wp_nil fun y₉ => ?_))
  have k₉ : Only [.a0, .a1] t₃ t₉ := (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans o₉))))).mono
  have b₉ := b₃.only P.fits k₉
  have r0' : (t₉.gpr .a0 != 0) = decide (kk s - (2 * H.D + 2) < mLen s) := by
    rw [e₉, e₈, o₇.get .t3, o₆.get .t3, o₅.get .t3, o₄.get .t3, k₃.get .t3, E.t3, o₈.get .a1, e₇, e₆,
      o₅.get .t3, o₄.get .t3, k₃.get .t3, E.t3, e₅, o₄.get .s1, k₃.get .s1, b.s1, e₄,
      ← ofNat_toNat (s.gpr .a3), ← ofNat_toNat (stackArg s 1), Offset.ofNat_sub_ofNat hk]
    exact msgBit (by omega) (stackArg s 1).isLt
  have E₉ : Entered s t₉ := ⟨b₉, by rw [k₉.get .s6, k₃.get .s6]; exact E.s6,
    by rw [k₉.get .s7, k₃.get .s7]; exact E.s7, by rw [k₉.get .t2, k₃.get .t2]; exact E.t2,
    by rw [k₉.get .t3, k₃.get .t3]; exact E.t3, by rw [k₉.get .t4, k₃.get .t4]; exact E.t4⟩
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_done hHl P b₉
    (by rw [r0'] at hc; simp at hc; omega)) (fun hc => main_done hH hG fH fG hHh hHl hGh hGl hGv P T E₉
    (y₉.trans (y₃.trans hsy)) (by rw [r0'] at hc; simp at hc; omega))

theorem code_ok : WP isa (encrypt H f) s (Post Hs Gs s) := by
  refine WP.alloc (by decide) (by have := P.sp1; unfold frameBytes; unfold stackBytes at this; omega) ?_
  refine WP.seq (WP.mono_syms (entry_ok P) fun t E sy => WP.seq (WP.mono
    (checks_done hH hG fH fG hHh hHl hGh hGl hGv P T E sy) fun t' ⟨sv, res⟩ =>
      WP.mono (restore_ok sv (fb_al8 P)) fun w ⟨habi, h3, hm⟩ => ⟨habi, fun hc => ?_⟩))
  show Spec.Rsa.written w.mem _ _ ((w.gpr .a0).setWidth 32) _
  rw [hm, h3]
  exact res hc

end

/-- MGF1's table, on entry, if it is `w`'s: what MGF1 needs of it. -/
theorem tabS_entry {Hs : Spec.Mgf1.Hash} {vs : List TVar} (hc : Coh vs) {s : State}
    (h : (encSpec Hs (tables vs)).pre s) {w : TVar} (hw : w ∈ vs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 7) (FnTable.words isa s (Proof.HashTable.RISCV64.tableOf w))) :
    TabS w.H (fnsOf vs) 7 S s (stackArg s 7) := by
  have P := preO_of h
  refine Proof.HashTable.RISCV64.tabS_of (by decide) rfl (arg_al P (by decide)) P.al7 P.wt (A := aR s)
    (by rw [P.hrd]; simp) (in_aR (by decide)) ?_ P.ka (P.sa.sub_left (sc_sub P))
    (by rw [P.hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))) P.kt
    (P.st.sub_left (sc_sub P)) hc (spec_tab h).2 hw hh
  rw [stackArgAddr_eq]
  exact Offset.sub_base _ (by omega)

/-- MGF1's table, on entry: one of the tables of `vs`, which holds what MGF1
needs of it and names its hash function. -/
theorem tab_of {Hs : Spec.Mgf1.Hash} {vs : List TVar} (hc : Coh vs) {s : State}
    (h : (encSpec Hs (tables vs)).pre s) :
    ∃ w ∈ vs, TabS w.H (fnsOf vs) 7 S s (stackArg s 7) ∧
      Spec.HashTable.hashAt 64 s.mem (stackArg s 7) = some w.l.G := by
  obtain ⟨⟨T, hT, hh⟩, -⟩ := spec_tab h
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  exact ⟨w, hw, tabS_entry hc h hw hh,
    Proof.HashTable.RISCV64.hashAt_tableOf (Proof.HashTable.RISCV64.held_tableOf hh).2.1⟩

section
variable {H : Hash} (hH : HashOK H) (fH : FitsF H) {Hs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D)
include hH fH hHh hHl

/-- The correctness of `vg_rsa_oaep_<H>_mgf1_encrypt_precomputed`, against
its contract, for the tables of `vs`. -/
theorem code_correct {vs : List TVar} (hc : Coh vs) (s : State) (h : (encSpec Hs (tables vs)).pre s) :
    ∃ t s', Exec isa (encrypt H (fnsOf vs)) s t s' ∧ abiPreserved s s' ∧ (encSpec Hs (tables vs)).post s s' := by
  obtain ⟨w, -, T, hT⟩ := tab_of hc h
  have P : PreO H.D s := hHl ▸ preO_of h
  obtain ⟨t, s', he, habi, hr⟩ := code_ok hH w.l.ok fH w.l.fits hHh hHl w.l.hash w.l.len w.l.valid P T
  refine ⟨t, s', he, habi, ?_⟩
  unfold encSpec
  sig_post [Spec.RsaOaep.encryptTableContract, Spec.RsaOaep.encryptTableSig, Spec.RsaOaep.encryptPrecomputedSig,
    Spec.HashTable.param, Abi.withTables, abi, argRegs, stackArgs_eight, List.append_eq]
  intro G hG
  rw [hT] at hG
  cases hG
  exact hr

end

end VG.Proof.RsaOaep.RISCV64
