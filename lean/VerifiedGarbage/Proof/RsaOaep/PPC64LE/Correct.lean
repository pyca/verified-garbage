module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Pub
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
public import VerifiedGarbage.Proof.HashTable.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.ByLen

/-!
# RSAES-OAEP encryption on PPC64LE: correctness

Untrusted: everything here is checked by Lean. The checks of the lengths
(`chkK`, `chkMsg`: `k < 2 hLen + 2` and `msg_len > k - 2 hLen - 2`, from the
top bits of differences), then either zeros and 0 (`fail_ok`) or `EM`
(`em_ok`, `mask_ok`, with the hash functions the tables') and RSAEP of it
(`call_ok`): if `pre` holds the modulus' values, RSAES-OAEP-ENCRYPT (RFC 8017
§7.1.1), all for the digest length of the label's table (`byLen_ok`,
`checks_D`). `code_correct`: the function against its contract, for tables
of `vs` (`tab_of`: each table is one of them, whose hash function it
names).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_sub wp_lsr wp_or wp_nil eval_nonzero)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.HashTable.PPC64LE (TVar tables fnsOf Coh)
open VG.Impl.RsaOaep.PPC64LE (tword)

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

theorem entered_only {s t t' : State} {rs : List Reg} {D : Nat} (P : PreO D s) (E : Entered s t)
    (o : Only rs t t') (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs ++ ([.r9, .r10, .r11] : List Reg) := by decide) : Entered s t' := by
  have g : ∀ r ∈ [Reg.r9, .r10, .r11], t'.gpr r = t.gpr r := fun r hr =>
    o.gpr r fun h => hrs r h (List.mem_append_right _ hr)
  exact ⟨E.base.only P.fits o fun r h h' => hrs r h (List.mem_append_left _ h'), (g _ (by decide)).trans E.r9,
    (g _ (by decide)).trans E.r10, (g _ (by decide)).trans E.r11⟩

/-- The code for a digest length, which is all it uses of the hash
function's shape. -/
theorem checks_D {G G' : Hash} (hD : G.D = G'.D) (f : Fns) : checks G f = checks G' f := by
  simp only [checks, encMain, encEm, copySeed, chkK, chkMsg, copyLh, dbArgs, seedArgs, hD]

/-- The result and `out`, from the entry state `s`: the octets `encrypt`
returns, or zeros. -/
def Post (Hs Gs : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ (PreOk s →
    Spec.Rsa.written s'.mem (s.gpr .r3) (kk s) ((s'.gpr .r3).setWidth 32)
      (Spec.RsaOaep.encrypt Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (kk s))
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) (labB s) (msgB s) (seedB Hs.len s)))

/-- Before the restores. -/
def Done (Hs Gs : Spec.Mgf1.Hash) (s t : State) : Prop :=
  Saves s t ∧ (PreOk s →
    Spec.Rsa.written t.mem (s.gpr .r3) (kk s) ((t.gpr .r3).setWidth 32)
      (Spec.RsaOaep.encrypt Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (kk s))
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) (labB s) (msgB s) (seedB Hs.len s)))

section
variable {H G : Hash} (hH : HashOK H) (hG : HashOK G) {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
  {f : Fns} {s : State} (P : PreO H.D s) (T : TabS G f 9 S s (stackArg s 9)) (TL : TabS H f 8 S s (stackArg s 8))
include hH hG hHh hHl hGh hGl hGv P T TL

omit hH hG hHh hGh hGl hGv T TL in
theorem fail_done {t : State} (h : Base S vO s t) (hl : kk s < 2 * H.D + 2 + mLen s) :
    WP isa encFail t (Done Hs Gs s) :=
  WP.mono (fail_ok P h) fun t' ⟨sv, h3, hb⟩ => ⟨sv, fun _ => by
    rw [Proof.RsaOaep.encrypt_none (by rw [bytesAt_length, bytesAt_length, hHl]; exact hl), h3]
    exact ⟨rfl, hb⟩⟩

theorem main_done {t : State} (E : Entered s t) (hsy : t.syms = s.syms) (hk : 2 * H.D + 2 + mLen s ≤ kk s) :
    WP isa (encMain H f) t (Done Hs Gs s) := by
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  refine em_ok P hH TL hHh rfl E hsy hk fun t₁ b₁ y₁ he => ?_
  refine mask_ok P hG T hGh hGl hGv rfl hD0 hD64 (bytesAt_length _ _ _)
    (by rw [hHh, hH.hashLen]) (bytesAt_length _ _ _) hk b₁ (y₁.trans hsy) he fun t₂ b₂ hem => ?_
  refine WP.seq (WP.mono (pubArgs_ok P b₂ hem) fun t₃ a₃ => WP.mono (call_ok P a₃) fun t₄ ⟨sv, res⟩ =>
    ⟨sv, fun hc => ?_⟩)
  have hs : (seedB Hs.len s).length = Hs.len := bytesAt_length _ _ _
  rw [Proof.RsaOaep.encrypt_some hs (by rw [bytesAt_length, bytesAt_length, hHl]; exact hk), bytesAt_length,
    bytesAt_length, hHl]
  exact res hc

theorem checks_done {t : State} (E : Entered s t) (hsy : t.syms = s.syms) : WP isa (checks H f) t (Done Hs Gs s) := by
  have hD64 := hH.hD64
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r6).toNat := rfl
  have b := E.base
  refine WP.seq (WP.of_syms (wp_li (by omega_arith) fun t₁ o₁ e₁ => wp_sub fun t₂ o₂ e₂ => wp_lsr fun t₃ o₃ e₃ =>
    wp_nil fun y₃ => ?_))
  have k₃ : Only [.r3] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  have b₃ := b.only P.fits k₃
  have r3 : (t₃.gpr .r3 != 0) = decide (kk s < 2 * H.D + 2) := by
    rw [e₃, e₂, e₁, o₁.get .r15, b.r15, ← ofNat_toNat (s.gpr .r6)]
    exact ne_zero_ltBit (by omega_arith) (by omega_arith)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_done hHl P b₃
    (by rw [r3] at hc; simp at hc; omega_arith)) (fun hc => ?_)
  have hk : 2 * H.D + 2 ≤ kk s := by rw [r3] at hc; simp at hc; omega_arith
  refine WP.seq (WP.of_syms (wp_li (by omega_arith) fun t₄ o₄ e₄ => wp_sub fun t₅ o₅ e₅ => wp_sub fun t₆ o₆ e₆ =>
    wp_lsr fun t₇ o₇ e₇ => wp_lsr fun t₈ o₈ e₈ => wp_or fun t₉ o₉ e₉ => wp_nil fun y₉ => ?_))
  have k₉ : Only [.r3, .r4] t₃ t₉ := (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans o₉))))).mono
  have b₉ := b₃.only P.fits k₉
  have r3' : (t₉.gpr .r3 != 0) = decide (kk s - (2 * H.D + 2) < mLen s) := by
    rw [e₉, e₈, o₇.get .r10, o₆.get .r10, o₅.get .r10, o₄.get .r10, k₃.get .r10, E.r10, o₈.get .r4, e₇, e₆,
      o₅.get .r10, o₄.get .r10, k₃.get .r10, E.r10, e₅, o₄.get .r15, k₃.get .r15, b.r15, e₄,
      ← ofNat_toNat (s.gpr .r6), ← ofNat_toNat (stackArg s 1), Offset.ofNat_sub_ofNat hk]
    exact msgBit (by omega_arith) (stackArg s 1).isLt
  have E₉ : Entered s t₉ := ⟨b₉, by rw [k₉.get .r9, k₃.get .r9]; exact E.r9,
    by rw [k₉.get .r10, k₃.get .r10]; exact E.r10, by rw [k₉.get .r11, k₃.get .r11]; exact E.r11⟩
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_done hHl P b₉
    (by rw [r3'] at hc; simp at hc; omega_arith)) (fun hc => main_done hH hG hHh hHl hGh hGl hGv P T TL E₉
    (y₉.trans (y₃.trans hsy)) (by rw [r3'] at hc; simp at hc; omega_arith))

theorem code_ok (hl : H.D ∈ lens) : WP isa (encrypt f) s (Post Hs Gs s) := by
  have hD64 := hH.hD64
  refine WP.alloc (by decide) (by have := P.sp1; unfold frameBytes; omega_arith) ?_
  refine WP.seq (WP.mono_syms (entry_ok P) fun t E sy => ?_)
  -- The label's hash function's digest length to `r3`.
  refine WP.seq (WP.of_syms ?_)
  show WP isa (.block (tword .r3 8 4 ++ [])) t _
  refine wp_tword TL E.base (k := 4) (by decide) (d := .r3) (by decide) fun t₁ o₁ e₁ => wp_nil fun y₁ => ?_
  have e3 : t₁.gpr .r3 = BitVec.ofNat 64 H.D := e₁.trans TL.d
  -- The code for that length.
  refine WP.seq (byLen_ok (D := H.D) (by omega)
    (F := fun u => Entered s u ∧ u.syms = s.syms ∧ u.gpr .r3 = BitVec.ofNat 64 H.D)
    (fun _ h => h.2.2) (fun u u' ⟨E', y', r3'⟩ o y => ⟨entered_only P E' o, y.trans y',
      by rw [o.get .r3]; exact r3'⟩) ?_ hl (fun x hx => (lens_certs x hx).1) t₁
    ⟨entered_only P E o₁, y₁.trans sy, e3⟩)
  intro u ⟨E', y', _⟩
  rw [checks_D (G := ofLen H.D) (G' := H) rfl]
  exact WP.mono (checks_done hH hG hHh hHl hGh hGl hGv P T TL E' y') fun t' ⟨sv, res⟩ =>
    WP.mono (restore_ok sv) fun w ⟨habi, h3, hm⟩ => ⟨habi, fun hc => by rw [freed_mem, freed_gpr, hm, h3]; exact res hc⟩

end

/-- The label's hash function's table, on entry, if it is `w`'s: what its
calls need of it. -/
theorem tabS_entryL {D : Nat} {vs : List TVar} (hc : Coh vs) {s : State} (P : PreO D s)
    (hpw : (Proof.HashTable.PPC64LE.names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {w : TVar}
    (hw : w ∈ vs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 8) (FnTable.words isa s (Proof.HashTable.PPC64LE.tableOf w))) :
    TabS w.H (fnsOf vs) 8 S s (stackArg s 8) := by
  refine Proof.HashTable.PPC64LE.tabS_of (by decide) rfl (A := aR s) (by rw [P.hrd]; simp)
    (in_aR (by decide)) ?_ P.ka (P.sa.sub_left (sc_sub P)) (by
      rw [P.hrd]; iterate 6 apply List.mem_cons_of_mem
      exact List.mem_cons_self ..) P.ktl
    (P.stl.sub_left (sc_sub P)) hc hpw hw hh
  rw [stackArgAddr_eq]
  exact Offset.sub_base _ (by omega)

/-- MGF1's table, on entry, if it is `w`'s: what MGF1 needs of it. -/
theorem tabS_entry {D : Nat} {vs : List TVar} (hc : Coh vs) {s : State} (P : PreO D s)
    (hpw : (Proof.HashTable.PPC64LE.names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {w : TVar}
    (hw : w ∈ vs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 9) (FnTable.words isa s (Proof.HashTable.PPC64LE.tableOf w))) :
    TabS w.H (fnsOf vs) 9 S s (stackArg s 9) := by
  refine Proof.HashTable.PPC64LE.tabS_of (by decide) rfl (A := aR s) (by rw [P.hrd]; simp)
    (in_aR (by decide)) ?_ P.ka (P.sa.sub_left (sc_sub P)) (by
      rw [P.hrd]; iterate 7 apply List.mem_cons_of_mem
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
  exact ⟨w₁, hw₁, w, hw, Proof.HashTable.PPC64LE.hashAt_tableOf (Proof.HashTable.PPC64LE.held_tableOf hh₁).2.1,
    Proof.HashTable.PPC64LE.hashAt_tableOf (Proof.HashTable.PPC64LE.held_tableOf hh).2.1,
    fun P => ⟨tabS_entryL hc P hpw' hw₁ hh₁, tabS_entry hc P hpw' hw hh⟩⟩

/-- The digest length of a hash function the label may be hashed with is
one `byLen` takes. -/
theorem Link.lens_mem {H : Hash} (l : Link H) : H.D ∈ Impl.RsaOaep.PPC64LE.lens := by
  rw [← l.len]
  exact (show ∀ G ∈ labelHashes, G.len ∈ Impl.RsaOaep.PPC64LE.lens by decide) _ l.mem

/-- The correctness of `vg_rsa_oaep_encrypt_precomputed`, against its
contract, for the tables of `vs`. -/
theorem code_correct {vs : List TVar} (hc : Coh vs) (s : State) (h : (encSpec (tables vs)).pre s) :
    ∃ t s', Exec isa (encrypt (fnsOf vs)) s t s' ∧ abiPreserved s s' ∧ (encSpec (tables vs)).post s s' := by
  obtain ⟨w₁, -, w, -, hH, hG, hT⟩ := tab_of hc h
  have P : PreO w₁.H.D s := w₁.l.len ▸ preO_of h hH
  obtain ⟨TL, T⟩ := hT P
  obtain ⟨t, s', he, habi, hr⟩ := code_ok w₁.l.ok w.l.ok w₁.l.hash w₁.l.len w.l.hash w.l.len w.l.valid P T TL
    w₁.l.lens_mem
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

end VG.Proof.RsaOaep.PPC64LE
