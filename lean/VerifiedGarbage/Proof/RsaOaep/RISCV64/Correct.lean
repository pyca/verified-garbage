module

-- separate module: it builds in parallel with the constant-time proofs that do not need it (`CTBase`,
-- `CTBlocks`).
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Pub
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Hashes
public import VerifiedGarbage.Proof.HashTable.RISCV64
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.ByLen
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

theorem entered_only {s t t' : State} {rs : List Reg} {D : Nat} (P : PreO D s) (E : Entered s t)
    (o : Only rs t t')
    (hrs : ∀ r ∈ rs, r ∉ fixed ++ ([.s6, .s7, .t2, .t3, .t4] : List Reg) := by decide) : Entered s t' := by
  have g : ∀ r ∈ [Reg.s6, .s7, .t2, .t3, .t4], t'.gpr r = t.gpr r := fun r hr =>
    o.gpr r fun h => hrs r h (List.mem_append_right _ hr)
  exact ⟨E.base.only P.fits o fun r h h' => hrs r h (List.mem_append_left _ h'), (g _ (by decide)).trans E.s6,
    (g _ (by decide)).trans E.s7, (g _ (by decide)).trans E.t2, (g _ (by decide)).trans E.t3,
    (g _ (by decide)).trans E.t4⟩

/-- The code for a digest length, which is all it uses of the hash
function's shape. -/
theorem checks_D {G G' : Hash} (hD : G.D = G'.D) (f : Fns) : checks G f = checks G' f := by
  simp only [checks, encMain, encEm, copySeed, chkK, chkMsg, copyLh, dbArgs, seedArgs, hD]

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
  {f : Fns} {s : State} (P : PreO H.D s) (T : TabS G f 9 S s (stackArg s 9)) (TL : TabS H f 8 S s (stackArg s 8))
include hH hG fH fG hHh hHl hGh hGl hGv P T TL

omit hH hG fH fG hHh hGh hGl hGv T TL in
theorem fail_done {t : State} (h : Base S vO s t) (hl : kk s < 2 * H.D + 2 + mLen s) :
    WP isa encFail t (Done Hs Gs s) :=
  WP.mono (fail_ok P h) fun t' ⟨sv, h3, hb⟩ => ⟨sv, fun _ => by
    rw [Proof.RsaOaep.encrypt_none (by rw [bytesAt_length, bytesAt_length, hHl]; exact hl), h3]
    exact ⟨rfl, hb⟩⟩

theorem main_done {t : State} (E : Entered s t) (hsy : t.syms = s.syms) (hk : 2 * H.D + 2 + mLen s ≤ kk s) :
    WP isa (encMain H f) t (Done Hs Gs s) := by
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  refine em_ok P hH fH TL hHh rfl E hsy hk fun t₁ b₁ y₁ he => ?_
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
    (by rw [r0'] at hc; simp at hc; omega)) (fun hc => main_done hH hG fH fG hHh hHl hGh hGl hGv P T TL E₉
    (y₉.trans (y₃.trans hsy)) (by rw [r0'] at hc; simp at hc; omega))

theorem code_ok (hl : H.D ∈ lens) : WP isa (encrypt f) s (Post Hs Gs s) := by
  have hD64 := hH.hD64
  refine WP.alloc (by decide) (by have := P.sp1; unfold frameBytes; unfold stackBytes at this; omega) ?_
  refine WP.seq (WP.mono_syms (entry_ok P) fun t E sy => ?_)
  -- The label's hash function's digest length to `a0`.
  refine WP.seq (WP.of_syms ?_)
  show WP isa (.block (tword .a0 8 4 ++ [])) t _
  refine wp_tword TL E.base (k := 4) (by decide) (d := .a0) fun t₁ o₁ e₁ => wp_nil fun y₁ => ?_
  have e0 : t₁.gpr .a0 = BitVec.ofNat 64 H.D := e₁.trans TL.d
  -- The code for that length.
  refine WP.seq (byLen_ok (D := H.D) (by omega)
    (F := fun u => Entered s u ∧ u.syms = s.syms ∧ u.gpr .a0 = BitVec.ofNat 64 H.D)
    (fun _ h => h.2.2) (fun u u' ⟨E', y', r0'⟩ o y => ⟨entered_only P E' o, y.trans y',
      by rw [o.get .a0]; exact r0'⟩) ?_ hl (fun x hx => (lens_certs x hx).1) t₁
    ⟨entered_only P E o₁, y₁.trans sy, e0⟩)
  intro u ⟨E', y', _⟩
  rw [checks_D (G := ofLen H.D) (G' := H) rfl]
  exact WP.mono (checks_done hH hG fH fG hHh hHl hGh hGl hGv P T TL E' y') fun t' ⟨sv, res⟩ =>
    WP.mono (restore_ok sv (fb_al8 P)) fun w ⟨habi, h3, hm⟩ => ⟨habi, fun hc => by
      show Spec.Rsa.written w.mem _ _ ((w.gpr .a0).setWidth 32) _
      rw [hm, h3]
      exact res hc⟩

end

/-- The label's hash function's table, on entry, if it is `w`'s: what its
calls need of it. -/
theorem tabS_entryL {D : Nat} {vs : List TVar} (hc : Coh vs) {s : State} (P : PreO D s)
    (hpw : (Proof.HashTable.RISCV64.names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {w : TVar}
    (hw : w ∈ vs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 8) (FnTable.words isa s (Proof.HashTable.RISCV64.tableOf w))) :
    TabS w.H (fnsOf vs) 8 S s (stackArg s 8) := by
  refine Proof.HashTable.RISCV64.tabS_of (by decide) rfl (arg_al P (by decide)) P.al8 P.wtl (A := aR s)
    (by rw [P.hrd]; simp) (in_aR (by decide)) ?_ P.ka (P.sa.sub_left (sc_sub P))
    (by rw [P.hrd]; iterate 6 apply List.mem_cons_of_mem
        exact List.mem_cons_self ..) P.ktl
    (P.stl.sub_left (sc_sub P)) hc hpw hw hh
  rw [stackArgAddr_eq]
  exact Offset.sub_base _ (by omega)

/-- MGF1's table, on entry, if it is `w`'s: what MGF1 needs of it. -/
theorem tabS_entry {D : Nat} {vs : List TVar} (hc : Coh vs) {s : State} (P : PreO D s)
    (hpw : (Proof.HashTable.RISCV64.names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {w : TVar}
    (hw : w ∈ vs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 9) (FnTable.words isa s (Proof.HashTable.RISCV64.tableOf w))) :
    TabS w.H (fnsOf vs) 9 S s (stackArg s 9) := by
  refine Proof.HashTable.RISCV64.tabS_of (by decide) rfl (arg_al P (by decide)) P.al7 P.wt (A := aR s)
    (by rw [P.hrd]; simp) (in_aR (by decide)) ?_ P.ka (P.sa.sub_left (sc_sub P))
    (by rw [P.hrd]; iterate 7 apply List.mem_cons_of_mem
        exact List.mem_cons_self ..) P.kt
    (P.st.sub_left (sc_sub P)) hc hpw hw hh
  rw [stackArgAddr_eq]
  exact Offset.sub_base _ (by omega)

/-- The tables, on entry: each one of the tables of `vs`, which names its
hash function, and holds what the calls through it need. -/
theorem tab_of {vs : List TVar} (hc : Coh vs) {s : State} (h : (encSpec (tables vs)).pre s) :
    ∃ w₁ ∈ vs, ∃ w ∈ vs, Spec.HashTable.hashAt 64 s.mem (stackArg s 8) = some w₁.l.G ∧
      Spec.HashTable.hashAt 64 s.mem (stackArg s 9) = some w.l.G ∧
      ∀ {D : Nat}, PreO D s → TabS w₁.H (fnsOf vs) 8 S s (stackArg s 8) ∧ TabS w.H (fnsOf vs) 9 S s (stackArg s 9) := by
  obtain ⟨⟨T₁, hT₁, hh₁⟩, ⟨T, hT, hh⟩, hpw⟩ := spec_tab h
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  have hpw' := hpw.sublist (List.sublist_append_left _ _)
  exact ⟨w₁, hw₁, w, hw, Proof.HashTable.RISCV64.hashAt_tableOf (Proof.HashTable.RISCV64.held_tableOf hh₁).2.1,
    Proof.HashTable.RISCV64.hashAt_tableOf (Proof.HashTable.RISCV64.held_tableOf hh).2.1,
    fun P => ⟨tabS_entryL hc P hpw' hw₁ hh₁, tabS_entry hc P hpw' hw hh⟩⟩

/-- The correctness of `vg_rsa_oaep_encrypt_precomputed`, against its
contract, for the tables of `vs`. -/
theorem code_correct {vs : List TVar} (hc : Coh vs) (s : State) (h : (encSpec (tables vs)).pre s) :
    ∃ t s', Exec isa (encrypt (fnsOf vs)) s t s' ∧ abiPreserved s s' ∧ (encSpec (tables vs)).post s s' := by
  obtain ⟨w₁, -, w, -, hH, hG, hT⟩ := tab_of hc h
  have P : PreO w₁.H.D s := w₁.l.len ▸ preO_of h hH
  obtain ⟨TL, T⟩ := hT P
  obtain ⟨t, s', he, habi, hr⟩ := code_ok w₁.l.ok w.l.ok w₁.l.fits w.l.fits w₁.l.hash w₁.l.len w.l.hash w.l.len
    w.l.valid P T TL w₁.l.lens_mem
  refine ⟨t, s', he, habi, ?_⟩
  unfold encSpec
  sig_post [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig,
    Spec.HashTable.param, Abi.withTables, abi, argRegs, stackArgs_ten, List.append_eq]
  intro H' G' hH' hG'
  rw [hH] at hH'
  rw [hG] at hG'
  cases hH'
  cases hG'
  exact hr

end VG.Proof.RsaOaep.RISCV64
