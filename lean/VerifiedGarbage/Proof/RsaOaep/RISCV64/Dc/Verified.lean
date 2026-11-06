module

import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Correct
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTMgfT
public import VerifiedGarbage.Proof.HashTable.RISCV64
public import VerifiedGarbage.Proof.Mgf1.Basic
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.CTLabel
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.CTPriv
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.CTBlocks
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Label
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Scan
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Buf
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Shift
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Out
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Unmask
import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBlocks
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Main
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.CTBase
public import VerifiedGarbage.Proof.RsaOaep.Scan
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.ByLen

/-!
# RSAES-OAEP decryption on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/CTMain.lean`, `Dc/Verified.lean`): constant time
(`code_constantTime`, from `code_ct`, for the tables of the first run,
which the public data makes the second's); a state meeting the
precondition, with both tables that of any `w` of `vs`, at `0x300000`
(`dec_sat`); and `dec_verified`.
-/

@[expose] public section

/-!
## RSAES-OAEP decryption on RISC-V: constant time

Two runs from entry states with the anchor's public data leak alike: the
code between the calls by the taint analysis (`Dc/CTBlocks`), the private
operation by its constant time (`priv_ct`), the hash functions' calls by
their contracts through the tables (`hashLabelT_ct`, MGF1's `mgfXorT_ctS`,
with each table at the same address and its functions at the same
addresses: `DXT`), the branch on the label's public digest length
(`byLen_ct`) and that on the public `k` (`two_ite`); what each run satisfies between them
follows from correctness. The scan's index, the shift's count and the
private operation's result differ between the runs, but only as data.
-/

namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.Impl.RsaOaep.RISCV64.Dec
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Two Pins two_post two_ite two_alloc wp_li wp_addi wp_subi wp_nil wp_ld
  wp_addSp eval_nonzero)
open VG.Proof.RsaOaep.RISCV64 (Base Saves SC off offs MgfAT MFit HashCT TabS TabA BT two_seq mgfXorT_ok mgfXorT_ctS
  sub_k seedArgs_taint dbArgs_taint chkK_taint restore_taint hfits sc_in)
open VG.Proof.RsaOaep (scan_idx)
open VG.Proof.HashTable.RISCV64 (TVar tables fnsOf Coh)

/-- `k` passed the check, in terms of the anchor. -/
abbrev HK (D : Nat) (a : State) : Prop := 2 * D + 2 ≤ (a.gpr .a4).toNat

theorem hk_s {D : Nat} {a s : State} (p : PubD a s) (h : HK D a) : 2 * D + 2 ≤ kk s := by
  show 2 * D + 2 ≤ (s.gpr .a4).toNat; rw [p.g .a4 (by decide)]; exact h

/-- `G`'s functions at the anchor's addresses. -/
def SymG (G : Hash) (a s : State) : Prop :=
  s.syms G.initN = a.syms G.initN ∧ s.syms G.updN = a.syms G.updN ∧ s.syms G.finN = a.syms G.finN

/-- Both tables on entry: MGF1's, `G`'s, and the label's hash function's,
`H`'s. -/
def TT (G H : Hash) (f : Fns) (s : State) : Prop :=
  TabS G f 16 (SD s) s (stackArg s 16) ∧ TabS H f 15 (SD s) s (stackArg s 15)

/-- Both tables' functions at the anchor's addresses. -/
def SymGH (G H : Hash) (a s : State) : Prop := SymG G a s ∧ SymG H a s

/-- `DX`, with both tables on entry, their functions at the anchor's
addresses, and the entry's addresses of statics. -/
def DXT (G H : Hash) (f : Fns) (a t : State) : Prop :=
  ∃ s m, PreD s ∧ TT G H f s ∧ PubD a s ∧ SymGH G H a s ∧ Frame [kD s, scR s] s.mem m ∧
    Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t ∧ t.syms = s.syms

theorem DXT.dx {G H : Hash} {f : Fns} {a t : State} (h : DXT G H f a t) : DX a t :=
  let ⟨s, m, P, _, p, _, hm, b, _⟩ := h; ⟨s, m, P, p, hm, b⟩

theorem DXT.only {G H : Hash} {f : Fns} {a t t' : State} {rs : List Reg} (h : DXT G H f a t) (o : Only rs t t')
    (hy : t'.syms = t.syms) (hrs : ∀ r ∈ rs, r ∉ Proof.RsaOaep.RISCV64.fixed := by decide) : DXT G H f a t' :=
  let ⟨s, m, P, T, p, y, hm, b, sy⟩ := h
  ⟨s, m, P, T, p, y, hm, b.only (fits P (s' := withMem s m) rfl rfl) o hrs, hy.trans sy⟩

/-- The base state's precondition, with MGF1's table. -/
def PreXT (G : Hash) (f : Fns) (x : State) : Prop := PreX x ∧ TabS G f 16 SX x (stackArg x 16)

/-- The base state's public data, with MGF1's table's address and `G`'s
functions' addresses. -/
def PubXT (G : Hash) (a x : State) : Prop := PubX a x ∧ stackArg x 16 = stackArg a 16 ∧ SymG G a x

theorem okXT (G : Hash) (f : Fns) : Proof.RsaOaep.RISCV64.OkS SX (PreXT G f) (PubXT G) :=
  ⟨fun h => h.1, fun p => p.1.1, fun p => p.1.2⟩

theorem tabXT (G : Hash) (f : Fns) : TabA G f 16 SX (PreXT G f) (PubXT G) :=
  ⟨fun h => h.2, fun p => p.2.1, fun p => p.2.2.1, fun p => p.2.2.2.1, fun p => p.2.2.2.2⟩

/-- What the label's hash needs of the base state: the label readable, apart
from what the hash function writes in `scratch` and from the stack, and our
stack arguments readable, apart from the stack and `scratch`, at an aligned
stack pointer. -/
def LabX (H : Hash) (x : State) : Prop :=
  (⟨stackArg x 9, (stackArg x 10).toNat⟩ : Region) ∈ x.rd ∧
    Region.Disjoint ⟨stackArg x 9, (stackArg x 10).toNat⟩ ⟨off (SX x) oSt, H.S⟩ ∧
    (Proof.RsaOaep.RISCV64.cR x).Disjoint ⟨stackArg x 9, (stackArg x 10).toNat⟩ ∧ (stackArg x 10).toNat < 2 ^ 64 ∧
    aR x ∈ x.rd ∧ (Proof.RsaOaep.RISCV64.kR x).Disjoint (aR x) ∧ (SC SX x).Disjoint (aR x) ∧
    x.sp.toNat % 16 = 0 ∧ x.sp.toNat + 136 ≤ 2 ^ 64

/-- A load of the base state's stack argument `j` through `t6`, its stack
pointer, with memory as in the base state but for the stack and our part of
the working space. -/
theorem wp_argL {H : Hash} {x u : State} (L : LabX H x) {r : Reg} {j : Nat} {is : List Instr}
    {Q : State → Prop} (hj : j < 17) (h6 : u.gpr .t6 = x.sp) (hrd : u.rd = x.rd)
    (hmu : Frame [Proof.RsaOaep.RISCV64.kR x, SC SX x] x.mem u.mem)
    (k : ∀ u', Only [r] u u' → u'.gpr r = stackArg x j → WP isa (.block is) u' Q)
    (ho : 8 * j < 2048 := by decide) :
    WP isa (.block (.load .d r .t6 (8 * j) :: is)) u Q := by
  obtain ⟨-, -, -, -, hA, hkA, hsA, hal, hsp⟩ := L
  have e : (stackArgAddr x j).toNat = x.sp.toNat + 8 * j := by
    simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine wp_ld (a := stackArgAddr x j) (by rw [h6]; rfl) (by rw [e]; omega) ?_ (fun u' o e => k u' o ?_) ho
  · rw [hrd]; exact ⟨aR x, List.mem_append_left _ hA, in_aR hj⟩
  · rw [e, stackArg, hmu.readW (in_aR hj) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hkA.symm
      · exact hsA.symm) (by decide)]

/-- The base state's precondition, with both tables and the label. -/
def PreXL (G H : Hash) (f : Fns) (x : State) : Prop :=
  PreXT G f x ∧ TabS H f 15 SX x (stackArg x 15) ∧ LabX H x

/-- The base state's public data, with both tables' addresses, their
functions' addresses, and the label. -/
def PubXL (G H : Hash) (a x : State) : Prop :=
  PubXT G a x ∧ stackArg x 15 = stackArg a 15 ∧ SymG H a x ∧ stackArg x 9 = stackArg a 9 ∧
    stackArg x 10 = stackArg a 10

theorem okXL (G H : Hash) (f : Fns) : Proof.RsaOaep.RISCV64.OkS SX (PreXL G H f) (PubXL G H) :=
  ⟨fun h => h.1.1, fun p => p.1.1.1, fun p => p.1.1.2⟩

theorem tabXL (G H : Hash) (f : Fns) : TabA H f 15 SX (PreXL G H f) (PubXL G H) :=
  ⟨fun h => h.2.1, fun p => p.2.1, fun p => p.2.2.1.1, fun p => p.2.2.1.2.1, fun p => p.2.2.1.2.2⟩

/-- The base state of a run for the label's hash, from the decoding's. -/
theorem DXT.toL {G H : Hash} (hH : HashOK H) {f : Fns} {a t : State} (h : DXT G H f a t) :
    BT SX VX (PreXL G H f) (PubXL G H) a t := by
  obtain ⟨s, m, P, T, p, y, hm, b, sy⟩ := h
  have F := hfits hH
  obtain ⟨_, _, _, _, _⟩ := offs
  obtain ⟨pX, bX⟩ := toX P hm _ (rcOf_le _) b
  have a16 : stackArg (bx s m (rcOf (privO s))) 16 = stackArg s 16 := stackArg_bx P hm _ (by decide)
  have a15 : stackArg (bx s m (rcOf (privO s))) 15 = stackArg s 15 := stackArg_bx P hm _ (by decide)
  have a9 : stackArg (bx s m (rcOf (privO s))) 9 = stackArg s 9 := stackArg_bx P hm _ (by decide)
  have a10 : stackArg (bx s m (rcOf (privO s))) 10 = stackArg s 10 := stackArg_bx P hm _ (by decide)
  have h13 : SX (bx s m (rcOf (privO s))) = Sd s := stackArg_bx P hm _ (i := 13) (by decide)
  have eSC : SC SX (bx s m (rcOf (privO s))) = SC (SD s) s := by simp only [SC, h13]
  refine ⟨_, ⟨⟨pX, by rw [a16]; exact tabS_to P T.1 hm rfl rfl rfl (by simp only [SC, h13])⟩,
    by rw [a15]; exact tabS_toL P T.2 hm rfl rfl rfl (by simp only [SC, h13]), ?_⟩,
    ⟨⟨pubX_bx P hm p, a16.trans (p.args 16 (by decide)), y.1⟩, a15.trans (p.args 15 (by decide)), y.2,
      a9.trans (p.args 9 (by decide)), a10.trans (p.args 10 (by decide))⟩, bX, sy⟩
  show LabX H (bx s m (rcOf (privO s)))
  unfold LabX
  rw [a9, a10, h13, eSC]
  exact ⟨by show lR s ∈ s.rd; rw [P.hrd]; simp, (P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega)),
    P.kl.sub_left fun a ha => kR_sub a (Proof.RsaOaep.RISCV64.cR_sub (withMem s m) a ha), BitVec.isLt _,
    by show aR s ∈ s.rd; rw [P.hrd]; simp, P.ka.sub_left kR_sub, P.sa.sub_left (sc_sub P), P.spal, P.sp2⟩

/-- `DXT` with the check passed. -/
def DK (G H : Hash) (f : Fns) (D : Nat) (a t : State) : Prop := DXT G H f a t ∧ HK D a

/-- MGF1's arguments, from the anchor. -/
def MgfD (G H : Hash) (f : Fns) (src srcLen dst dstLen : Nat) (a t : State) : Prop :=
  DXT G H f a t ∧ t.gpr .s6 = off (stackArg a 13) src ∧ t.gpr .s7 = BitVec.ofNat 64 srcLen ∧
    t.gpr .s8 = off (stackArg a 13) dst ∧ t.gpr .s9 = BitVec.ofNat 64 dstLen

theorem MgfD.toA {G H : Hash} {f : Fns} {src srcLen dst dstLen : Nat} {a t : State}
    (h : MgfD G H f src srcLen dst dstLen a t) : MgfAT SX VX (PreXT G f) (PubXT G) src srcLen dst dstLen a t := by
  obtain ⟨⟨s, m, P, T, p, y, hm, b, sy⟩, h6, h7, h8, h9⟩ := h
  obtain ⟨pX, bX⟩ := toX P hm _ (rcOf_le _) b
  have a16 : stackArg (bx s m (rcOf (privO s))) 16 = stackArg s 16 := stackArg_bx P hm _ (by decide)
  have h13 : SX (bx s m (rcOf (privO s))) = Sd s := stackArg_bx P hm _ (i := 13) (by decide)
  refine ⟨_, ⟨pX, ?_⟩, ⟨pubX_bx P hm p, a16.trans (p.args 16 (by decide)), y.1⟩, bX, sy, h6, h7, h8, h9⟩
  rw [a16]
  exact tabS_to P T.1 hm rfl rfl rfl (by simp only [SC, h13])

section
variable {G H : Hash} (hG : HashOK G) (cG : HashCT hG) (hF : G.F ≤ 208) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {f : Fns}

include cG hF hGh hGl hGv in
/-- `mgfXorT`, with its lengths and offsets the anchor's. -/
theorem mgf_anyD (q : State → Nat × Nat × Nat × Nat) :
    RelCT isa (Two fun a t => MgfD G H f (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2 a t ∧
      MFit (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2) (mgfXorT f 16) fun _ _ => True :=
  (RelCT.exists_ (P := fun (x : {x : Nat × Nat × Nat × Nat // MFit x.1 x.2.1 x.2.2.1 x.2.2.2}) =>
      Two (MgfAT SX VX (PreXT G f) (PubXT G) x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    fun x => mgfXorT_ctS (okXT G f) hG cG hF x.2 hGh hGl hGv (tabXT G f)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨q a, h₁.2⟩, a, h₁.1.toA, h₂.1.toA⟩) fun _ _ h => h

include hF hGh hGl hGv in
theorem mgf_dx {src srcLen dst dstLen : Nat} (hf : MFit src srcLen dst dstLen) {a t : State}
    (h : MgfD G H f src srcLen dst dstLen a t) : WP isa (mgfXorT f 16) t (DXT G H f a) := by
  obtain ⟨⟨s, m, P, T, p, y, hm, b, sy⟩, h6, h7, h8, h9⟩ := h
  exact WP.mono (mgfXorT_ok (fits P (s' := withMem s m) rfl rfl) hG hF (tabS_wm P T.1 hm) hGh hGl hGv hf b sy
    (h6.trans (off13 p _)) h7 (h8.trans (off13 p _)) h9) fun _ h' => ⟨s, m, P, T, p, y, hm, h'.1.1, h'.2⟩

end

/-- `k` from the anchor. -/
abbrev kA (a : State) : Nat := (a.gpr .a4).toNat

theorem kA_le {a t : State} (h : DX a t) : kA a ≤ 1024 := by
  obtain ⟨s, m, P, p, -, -⟩ := h
  have := P.k2; rw [p.g .a4 (by decide)] at this; exact this

/-- The arguments of MGF1 of `maskedDB` into the seed. -/
theorem seed_wp {G H : Hash} {f : Fns} (hD0 : 0 < H.D) (hD64 : H.D ≤ 64) {a t : State} (h : DK G H f H.D a t) :
    WP isa (.block (seedArgs H)) t fun t' => (MgfD G H f (1 + H.D) (kA a - (H.D + 1)) 1 H.D a t' ∧
      MFit (1 + H.D) (kA a - (H.D + 1)) 1 H.D) ∧ HK H.D a := by
  obtain ⟨hE, -, -, -, -⟩ := offs
  have hk := h.2
  have hk2 := kA_le h.1.dx
  have ek : kA a = (a.gpr .a4).toNat := rfl
  obtain ⟨-, r0, r1, -, -⟩ := h.1.dx.pins
  refine WP.of_syms (wp_addi (imm := oEm + 1 + H.D) (h := by omega) fun t₁ o₁ e₁ =>
    wp_subi (imm := H.D + 1) (h := by omega) fun t₂ o₂ e₂ => wp_addi (imm := oEm + 1) (h := by omega)
    fun t₃ o₃ e₃ => wp_li (imm := H.D) (by omega) fun t₄ o₄ e₄ => wp_nil fun y => ?_)
  have k₄ : Only [.s6, .s7, .s8, .s9] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine ⟨⟨⟨h.1.only k₄ y, ?_, ?_, ?_, ?_⟩, ⟨by omega, by omega, .inr (by omega), by omega⟩⟩, hk⟩
  · rw [o₄.get .s6, o₃.get .s6, o₂.get .s6, e₁, r0, hE, Nat.zero_add]
  · rw [o₄.get .s7, o₃.get .s7, e₂, o₁.get .s1, r1, sub_k (by omega)]
  · rw [o₄.get .s8, e₃, o₂.get .s0, o₁.get .s0, r0, hE]
  · rw [e₄]

/-- The arguments of MGF1 of the seed into `maskedDB`. -/
theorem db_wp {G H : Hash} {f : Fns} (hD64 : H.D ≤ 64) {a t : State} (h : DK G H f H.D a t) :
    WP isa (.block (dbArgs H)) t fun t' => (MgfD G H f 1 H.D (1 + H.D) (kA a - (H.D + 1)) a t' ∧
      MFit 1 H.D (1 + H.D) (kA a - (H.D + 1))) ∧ HK H.D a := by
  obtain ⟨hE, -, -, -, -⟩ := offs
  have hk := h.2
  have hk2 := kA_le h.1.dx
  have ek : kA a = (a.gpr .a4).toNat := rfl
  obtain ⟨-, r0, r1, -, -⟩ := h.1.dx.pins
  refine WP.of_syms (wp_addi (imm := oEm + 1) (h := by omega) fun t₁ o₁ e₁ => wp_li (imm := H.D) (by omega)
    fun t₂ o₂ e₂ => wp_addi (imm := oEm + 1 + H.D) (h := by omega) fun t₃ o₃ e₃ =>
    wp_subi (imm := H.D + 1) (h := by omega) fun t₄ o₄ e₄ => wp_nil fun y => ?_)
  have k₄ : Only [.s6, .s7, .s8, .s9] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine ⟨⟨⟨h.1.only k₄ y, ?_, ?_, ?_, ?_⟩, ⟨by omega, by omega, .inl (by omega), by omega⟩⟩, hk⟩
  · rw [o₄.get .s6, o₃.get .s6, o₂.get .s6, e₁, r0, hE]
  · rw [o₄.get .s7, o₃.get .s7, e₂]
  · rw [o₄.get .s8, e₃, o₂.get .s0, o₁.get .s0, r0, hE, Nat.zero_add]
  · rw [e₄, o₃.get .s1, o₂.get .s1, o₁.get .s1, r1, sub_k (by omega)]

/-- `DXT` from an entry state with `a`'s public data, by the correctness
lemmas' `Base`. -/
theorem dk_wp {G H : Hash} {f : Fns} {D : Nat} {c : Prog isa} {a t : State} (h : DK G H f D a t)
    (hw : ∀ s m, PreD s → PubD a s → 2 * D + 2 ≤ kk s → Frame [kD s, scR s] s.mem m →
      Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t →
      WP isa c t fun t' => Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t') :
    WP isa c t (DK G H f D a) :=
  let ⟨⟨s, m, P, T, p, y, hm, b, sy⟩, hk⟩ := h
  WP.mono_syms (hw s m P p (hk_s p hk) hm b) fun _ b' y' => ⟨⟨s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩

/-- After the scan: the index, below `k`. -/
def DI (G H : Hash) (f : Fns) (D : Nat) (a t : State) : Prop :=
  DK G H f D a t ∧ ∃ idx, idx < kA a ∧ t.gpr .s6 = BitVec.ofNat 64 idx

theorem dk_pins {G H : Hash} {f : Fns} {D : Nat} {α : Type} {Φ : α → State → Prop} {an : α → State}
    (h : ∀ x t, Φ x t → DK G H f D (an x) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ [Reg.s0, .s1, .s2, .s3] := by decide) : Pins Φ rs :=
  dx_pins (fun x t hx => (h x t hx).1.dx) rs hrs

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (fH : H.F ≤ 208) (hG : HashOK G) (cG : HashCT hG)
  (fG : G.F ≤ 208) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {f : Fns}

include hH cH fH cG fG hGh hGl hGv in
theorem decMain_ct : RelCT isa (Two (DK G H f H.D)) (decMain H f) fun _ _ => True := by
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  unfold decMain
  -- The seed with MGF1 of `maskedDB`.
  let q₁ : State → Nat × Nat × Nat × Nat := fun a => (1 + H.D, kA a - (H.D + 1), 1, H.D)
  refine two_seq (Ψ := fun a t => (MgfD G H f (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2 a t ∧
      MFit (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2) ∧ HK H.D a)
    (seedArgs_taint H (dk_pins (an := id) (fun _ _ h => h) [])) (fun a t h => seed_wp hD0 hD64 h) ?_
  refine two_seq (Ψ := DK G H f H.D) ((mgf_anyD hG cG fG hGh hGl hGv q₁).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩) fun _ _ h => h)
    (fun a t ⟨⟨h, hf⟩, hk⟩ => WP.mono (mgf_dx hG fG hGh hGl hGv hf h) fun _ h' => ⟨h', hk⟩) ?_
  -- `maskedDB` with MGF1 of the seed.
  let q₂ : State → Nat × Nat × Nat × Nat := fun a => (1, H.D, 1 + H.D, kA a - (H.D + 1))
  refine two_seq (Ψ := fun a t => (MgfD G H f (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2 a t ∧
      MFit (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2) ∧ HK H.D a)
    (dbArgs_taint H (dk_pins (an := id) (fun _ _ h => h) [])) (fun a t h => db_wp hD64 h) ?_
  refine two_seq (Ψ := DK G H f H.D) ((mgf_anyD hG cG fG hGh hGl hGv q₂).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩) fun _ _ h => h)
    (fun a t ⟨⟨h, hf⟩, hk⟩ => WP.mono (mgf_dx hG fG hGh hGl hGv hf h) fun _ h' => ⟨h', hk⟩) ?_
  -- `lHash`, and `lHash'` against it.
  refine two_seq (Ψ := DK G H f H.D) ((hashLabelT_ct (vf := VX) (okXL G H f) hH cH fH (tabXL G H f)
      (R := fun _ _ => True) (L := fun x => stackArg x 9) (N := fun x => (stackArg x 10).toNat)
      (fun _ _ _ _ _ => trivial) (fun _ p => ⟨p.2.2.2.1, by rw [p.2.2.2.2]⟩)
      (fun P => ⟨P.2.2.1, P.2.2.2.1, P.2.2.2.2.1, P.2.2.2.2.2.1⟩) (fun h => lab2_taint h) (fun h => lab3_taint h)
      (fun ac t b _ => ?_) (fun ac t b _ => ?_)).mono
      (fun _ _ ⟨a, h₁, h₂⟩ => ⟨(a, 0), ⟨h₁.1.toL hH, trivial⟩, ⟨h₂.1.toL hH, trivial⟩⟩) fun _ _ h => h)
    (fun a t ⟨⟨s, m, P, T, p, y, hm, b, sy⟩, hk⟩ => WP.mono (hashLabelT_ok P hH fH hm (tabS_wmL P T.2 hm) b sy)
      fun t' ⟨⟨b', _⟩, y'⟩ => ⟨⟨s, m, P, T, p, y, hm, b', y'⟩, hk⟩) ?_
  · obtain ⟨x, PL, pL, bb, sy⟩ := b
    unfold argBase
    refine WP.of_syms (wp_addSp (imm := frameBytes) (fun t₁ o₁ e₁ => wp_addi (imm := oSt) fun t₂ o₂ e₂ =>
      wp_li (imm := 0) (by decide) fun t₃ o₃ e₃ => ?_) (by decide))
    have K₃ : Only [.t6, .a0, .a1] t t₃ := (o₁.trans (o₂.trans o₃)).mono
    have g6 : t₃.gpr .t6 = x.sp := by rw [o₃.get .t6, o₂.get .t6, e₁, bb.sv.sp, BitVec.sub_add_cancel]
    refine wp_argL PL.2.2 (j := 9) (by decide) g6 (K₃.rd.trans bb.rd) (by rw [K₃.mem]; exact bb.mem)
      fun t₄ o₄ e₄ => wp_argL PL.2.2 (j := 10) (by decide) (by rw [o₄.get .t6, g6])
        ((o₄.rd.trans K₃.rd).trans bb.rd) (by rw [o₄.mem, K₃.mem]; exact bb.mem) fun t₅ o₅ e₅ => wp_nil fun y => ?_
    have k : Only [.t6, .a0, .a1, .a2, .a3] t t₅ := (K₃.trans (o₄.trans o₅)).mono
    refine ⟨⟨x, PL, pL, bb.only ((okXL G H f).fits PL) k, y.trans sy⟩, trivial, ?_, ?_, ?_, ?_⟩
    · rw [o₅.get .a0, o₄.get .a0, o₃.get .a0, e₂, o₁.get .s0, bb.s0, (okXL G H f).S pL]
    · rw [o₅.get .a1, o₄.get .a1, e₃]; rfl
    · rw [o₅.get .a2, e₄, pL.2.2.2.1]
    · rw [e₅, pL.2.2.2.2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · obtain ⟨x, PL, pL, bb, sy⟩ := b
    unfold argBase
    refine WP.of_syms (wp_addSp (imm := frameBytes) (fun t₁ o₁ e₁ => wp_addi (imm := oSt) fun t₂ o₂ e₂ => ?_)
      (by decide))
    have g6 : t₂.gpr .t6 = x.sp := by rw [o₂.get .t6, e₁, bb.sv.sp, BitVec.sub_add_cancel]
    refine wp_argL PL.2.2 (j := 10) (by decide) g6 ((o₂.rd.trans o₁.rd).trans bb.rd)
      (by rw [o₂.mem, o₁.mem]; exact bb.mem) fun t₃ o₃ e₃ => wp_addi (imm := oDig) fun t₄ o₄ e₄ =>
        wp_nil fun y => ?_
    have k : Only [.t6, .a0, .a1, .a2] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    refine ⟨⟨x, PL, pL, bb.only ((okXL G H f).fits PL) k, y.trans sy⟩, ?_, ?_, ?_⟩
    · rw [o₄.get .a0, o₃.get .a0, e₂, o₁.get .s0, bb.s0, (okXL G H f).S pL]
    · rw [o₄.get .a1, e₃, pL.2.2.2.2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [e₄, o₃.get .s0, o₂.get .s0, o₁.get .s0, bb.s0, (okXL G H f).S pL]
  refine two_seq (Ψ := DK G H f H.D) (accLh_taint H (dk_pins (an := id) (fun _ _ h => h) [.s0]))
    (fun a t h => dk_wp h fun s m P _ hk _ b => WP.mono (accLh_ok P rfl hD0 hD64 hk b) fun _ h' => h'.1) ?_
  -- The scan.
  refine two_seq (Ψ := DI G H f H.D) (scan_taint H (dk_pins (an := id) (fun _ _ h => h) [.s0, .s1]))
    (fun a t ⟨⟨s, m, P, T, p, y, hm, b, sy⟩, hk⟩ => ?_) ?_
  · have hk' := hk_s p hk
    have hk2 := P.k2
    have ea : kA a = kk s := by show (a.gpr .a4).toNat = (s.gpr .a4).toNat; rw [p.g .a4 (by decide)]
    refine WP.mono_syms (scan_ok P rfl hD64 hk' b) fun t' ⟨b', _, _, _, i'⟩ y' =>
      ⟨⟨⟨s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩, ?_⟩
    obtain ⟨idx, he, hi⟩ := scan_idx (fun i => view t.mem (Sd s) (1 + 2 * H.D + i)) (t.gpr .s5)
      (kk s - (2 * H.D + 1))
    exact ⟨idx, by rw [ea]; omega, i'.trans he⟩
  -- The buffer.
  refine two_seq (Ψ := DI G H f H.D) (clearBuf_taint (dk_pins (an := id) (fun _ _ h => h.1) [.s0]))
    (fun a t ⟨⟨⟨s, m, P, T, p, y, hm, b, sy⟩, hk⟩, idx, hi, h6⟩ => WP.mono_syms (clearBuf_ok P b)
      fun t' ⟨b', g', _⟩ y' => ⟨⟨⟨s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩, idx, hi, (g'.get .s6).trans h6⟩) ?_
  refine two_seq (Ψ := DI G H f H.D) (copyT_taint H (dk_pins (an := id) (fun _ _ h => h.1) [.s0, .s1]))
    (fun a t ⟨⟨⟨s, m, P, T, p, y, hm, b, sy⟩, hk⟩, idx, hi, h6⟩ => WP.mono_syms (copyT_ok P rfl hD64 (hk_s p hk) b)
      fun t' ⟨b', g', _⟩ y' => ⟨⟨⟨s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩, idx, hi, (g'.get .s6).trans h6⟩) ?_
  -- The shift, `ok`, `out`, the length and the result.
  refine two_seq (Ψ := DK G H f H.D) (shift_taint (dk_pins (an := id) (fun _ _ h => h.1) [.s0, .s1]))
    (fun a t ⟨⟨⟨s, m, P, T, p, y, hm, b, sy⟩, hk⟩, idx, hi, h6⟩ => ?_) ?_
  · have ea : kA a = kk s := by show (a.gpr .a4).toNat = (s.gpr .a4).toNat; rw [p.g .a4 (by decide)]
    exact WP.mono_syms (shift_ok P b h6 (by rw [← ea]; exact hi)) fun _ h' y' =>
      ⟨⟨s, m, P, T, p, y, hm, h'.1, y'.trans sy⟩, hk⟩
  refine two_seq (Ψ := DK G H f H.D) (okMask_taint (dk_pins (an := id) (fun _ _ h => h) []))
    (fun a t h => dk_wp h fun s m P _ _ _ b => WP.mono (okMask_ok P b (rcOf_le _)) fun _ h' => h'.1) ?_
  refine two_seq (Ψ := fun a t => t.sp = fb a ∧ t.gpr .s3 = a.gpr .a2)
    (outLoop_taint (dk_pins (an := id) (fun _ _ h => h) [.s0, .s1, .s2])) (fun a t h => ?_) ?_
  · obtain ⟨-, -, -, -, r3⟩ := h.1.dx.pins
    obtain ⟨⟨s, m, P, -, p, -, hm, b, -⟩, -⟩ := h
    exact WP.mono (outLoop_ok P b) fun t' ⟨sv, _, g', _⟩ =>
      ⟨by rw [sv.sp, fb, fb, p.sp], (g'.get .s3).trans r3⟩
  exact decRet_taint H fun a t₁ t₂ h₁ h₂ => ⟨h₁.1.trans h₂.1.symm, fun r hr => by
    rw [List.mem_singleton.mp hr, h₁.2, h₂.2]⟩

end

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (fH : H.F ≤ 208) (hG : HashOK G) (cG : HashCT hG)
  (fG : G.F ≤ 208) {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)

/-- After the entry, from an entry state with MGF1's table, `G`'s, and `a`'s
public data. -/
def AEntT (G H : Hash) (f : Fns) (a t : State) : Prop :=
  ∃ s, PreD s ∧ TT G H f s ∧ PubD a s ∧ SymGH G H a s ∧ Entered s t ∧ t.syms = s.syms

/-- After the private operation, from such an entry state. -/
def AP (G H : Hash) (f : Fns) (a v : State) : Prop :=
  ∃ s, PreD s ∧ TT G H f s ∧ PubD a s ∧ SymGH G H a s ∧ AfterPriv s v ∧ v.syms = s.syms

/-- After the check of `k`. -/
def AC (G H : Hash) (f : Fns) (D : Nat) (a v : State) : Prop :=
  ∃ s, PreD s ∧ TT G H f s ∧ PubD a s ∧ SymGH G H a s ∧ AfterPriv s v ∧ v.syms = s.syms ∧
    (v.gpr .a0 != 0) = decide (kk s < 2 * D + 2)

theorem AC.dxt {G H : Hash} {f : Fns} {D : Nat} {a v : State} (h : AC G H f D a v) : DXT G H f a v :=
  let ⟨s, P, T, p, y, A, sy, _⟩ := h; ⟨s, v.mem, P, T, p, y, A.mem, A.base, sy⟩

theorem AC.dx {G H : Hash} {f : Fns} {D : Nat} {a v : State} (h : AC G H f D a v) : DX a v := h.dxt.dx

theorem AC.r0 {G H : Hash} {f : Fns} {D : Nat} {a v : State} (h : AC G H f D a v) :
    (v.gpr .a0 != 0) = decide (kA a < 2 * D + 2) := by
  obtain ⟨s, _, _, p, _, _, _, r⟩ := h
  rw [r]; show decide ((s.gpr .a4).toNat < _) = _; rw [p.g .a4 (by decide)]

theorem AP.dxt {G H : Hash} {f : Fns} {a v : State} (h : AP G H f a v) : DXT G H f a v :=
  let ⟨s, P, T, p, y, A, sy⟩ := h; ⟨s, v.mem, P, T, p, y, A.mem, A.base, sy⟩

theorem AP.only {G H : Hash} {f : Fns} {a v v' : State} {rs : List Reg} (h : AP G H f a v) (o : Only rs v v')
    (y : v'.syms = v.syms) (hrs : ∀ r ∈ rs, r ∉ Proof.RsaOaep.RISCV64.fixed := by decide) : AP G H f a v' :=
  let ⟨s, P, T, p, g, A, sy⟩ := h; ⟨s, P, T, p, g, A.only P o hrs, y.trans sy⟩

include hH cH fH hG cG fG hHh hHl hHv hGh hGl hGv in
theorem code_ct {f : Fns} (hl : H.D ∈ lens) :
    RelCT isa (Two fun a s => (PreD s ∧ TT G H f s) ∧ (PubD a s ∧ SymGH G H a s)) (decrypt f) fun _ _ => True := by
  have hD64 := hH.hD64
  refine two_alloc (R := fun _ _ => True) ?_
  refine two_seq (Ψ := AEntT G H f)
    (dentry_taint fun a u₁ u₂ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ =>
      ⟨by rw [e₁, e₂]; show s₁.sp - _ = s₂.sp - _; rw [h₁.2.1.sp, h₂.2.1.sp], fun _ h => nomatch h⟩)
    (fun a u ⟨s, ⟨⟨P, T⟩, ⟨p, g⟩⟩, e⟩ => by
      subst e; exact WP.mono_syms (entry_ok P) fun t E y => ⟨s, P, T, p, g, E, y⟩) ?_
  refine two_seq (Ψ := AP G H f) (priv_ct.mono (fun _ _ ⟨a, ⟨s₁, P₁, _, p₁, _, E₁, _⟩, ⟨s₂, P₂, _, p₂, _, E₂, _⟩⟩ =>
      ⟨a, ⟨s₁, P₁, p₁, E₁⟩, ⟨s₂, P₂, p₂, E₂⟩⟩) fun _ _ h => h)
    (fun a t ⟨s, P, T, p, g, E, sy⟩ => WP.mono_syms (priv_ok P E) fun v A y => ⟨s, P, T, p, g, A, y.trans sy⟩) ?_
  -- The label's hash function's digest length to `a0`.
  let A₃ := fun (a v : State) => AP G H f a v ∧ v.gpr .a0 = BitVec.ofNat 64 H.D
  have hlen : RelCT isa (Two (AP G H f)) (.block (lenLoad 15)) (Two A₃) :=
    (tword_two (okXL G H f) (tabXL G H f) (Φ := fun (ac : State × Nat) t => AP G H f ac.1 t)
      (fun _ _ h => h.dxt.toL hH) (d := .a0) (.inr (.inr rfl)) (k := 4) (by decide)
      (v := fun _ => BitVec.ofNat 64 H.D) fun P _ => P.2.1.d).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨(a, 0), h₁, h₂⟩)
      fun _ _ ⟨ac, ⟨t₁, h₁, o₁, z₁, e₁⟩, ⟨t₂, h₂, o₂, z₂, e₂⟩⟩ => ⟨ac.1, ⟨h₁.only o₁ z₁, e₁⟩, ⟨h₂.only o₂ z₂, e₂⟩⟩
  refine RelCT.seq hlen ?_
  -- The code for that length.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, PreD s ∧ PubD a s ∧ Saves s u)
    (byLen_ct (D := H.D) (Φ := A₃) (by omega) (fun _ _ h => h.2)
      (fun _ _ _ h₁ h₂ => h₁.1.dxt.dx.pins.1.trans h₂.1.dxt.dx.pins.1.symm)
      (fun _ _ _ ⟨h, r0⟩ o y => ⟨h.only o y, by rw [o.get .a0]; exact r0⟩) ?_ hl lens_certs)
    fun a v ⟨⟨s, P, T, p, g, A, sy⟩, h0⟩ => ?_)
    (restore_taint fun a u₁ u₂ ⟨s₁, _, p₁, v₁⟩ ⟨s₂, _, p₂, v₂⟩ =>
      ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.sp, p₂.sp], fun _ h => nomatch h⟩)
  · rw [decTail_D (G := ofLen H.D) (G' := H) rfl]
    refine two_seq (Ψ := AC G H f H.D) (chkK_taint H (dx_pins (an := id) (fun _ _ h => h.1.dxt.dx) []))
      (fun a v ⟨⟨s, P, T, p, g, A, sy⟩, _⟩ => WP.mono_syms (chk_ok P hH.hD64 A) fun _ ⟨A', r⟩ y =>
        ⟨s, P, T, p, g, A', y.trans sy, r⟩) ?_
    refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.r0, h₂.r0])
      (decFail_taint (dx_pins (an := id) (fun _ _ h => h.1.dx) [.s1, .s2, .s3])) ?_
    refine (decMain_ct hH cH fH hG cG fG hGh hGl hGv).mono (fun _ _ ⟨a, ⟨h₁, c₁⟩, ⟨h₂, _⟩⟩ => ?_) fun _ _ h => h
    rw [eval_nonzero, h₁.r0] at c₁
    have hk : HK H.D a := by simp at c₁; omega
    exact ⟨a, ⟨h₁.dxt, hk⟩, ⟨h₂.dxt, hk⟩⟩
  · refine byLen_ok (D := H.D) (by omega)
      (F := fun u => AfterPriv s u ∧ u.syms = s.syms ∧ u.gpr .a0 = BitVec.ofNat 64 H.D)
      (fun _ h => h.2.2) (fun u u' ⟨A', y', r0'⟩ o y => ⟨A'.only P o, y.trans y', by rw [o.get .a0]; exact r0'⟩)
      ?_ hl (fun x hx => (lens_certs x hx).1) v ⟨A, sy, h0⟩
    intro u ⟨A', y', _⟩
    rw [decTail_D (G := ofLen H.D) (G' := H) rfl]
    exact WP.seq (WP.mono (checks_done hH hG fH fG hHh hHl hHv hGh hGl hGv P T.1 T.2 A' y') fun v' h => WP.mono h
      fun _ d => ⟨s, P, p, d.1⟩)

end

theorem code_constantTime {vs : List TVar} (hc : Coh vs) :
    ConstantTime isa (decSpec (tables vs)).pre (decSpec (tables vs)).pub (decrypt (fnsOf vs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨⟨T₁, hT₁, hhL₁⟩, ⟨T, hT, hh₁⟩, hpw₁⟩ := spec_tabD h₁
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨p, hsy, hiffL, hiff⟩ := pubD_of hp
  have hhL₂ := (hiffL _ hT₁).mp hhL₁
  have hh₂ := (hiff _ hT).mp hh₁
  have q₁ := hpw₁.sublist (List.sublist_append_left _ _)
  have q₂ := (spec_tabD h₂).2.2.sublist (List.sublist_append_left _ _)
  have hn := Proof.HashTable.RISCV64.mem_names hw
  have hnL := Proof.HashTable.RISCV64.mem_names hw₁
  have P₁ := preD_of h₁
  have P₂ := preD_of h₂
  exact code_ct w₁.l.ok w₁.l.ct w₁.l.fits w.l.ok w.l.ct w.l.fits w₁.l.hash w₁.l.len w₁.l.valid w.l.hash w.l.len
    w.l.valid w₁.l.lens_mem _ _ _ _ _ _
    ⟨s₁, ⟨⟨P₁, tabS_entryD hc P₁ q₁ hw hh₁, tabS_entryDL hc P₁ q₁ hw₁ hhL₁⟩, pubD_refl s₁, ⟨rfl, rfl, rfl⟩,
        ⟨rfl, rfl, rfl⟩⟩,
      ⟨P₂, tabS_entryD hc P₂ q₂ hw hh₂, tabS_entryDL hc P₂ q₂ hw₁ hhL₂⟩, p,
      ⟨(hsy _ hn.1).symm, (hsy _ hn.2.1).symm, (hsy _ hn.2.2).symm⟩,
      ⟨(hsy _ hnL.1).symm, (hsy _ hnL.2.1).symm, (hsy _ hnL.2.2).symm⟩⟩ e₁ e₂

/-- `vg_rsa_oaep_decrypt` against its contract, for the tables of `vs`,
given a state meeting it. -/
theorem dec_verified {vs : List TVar} (hc : Coh vs) (hsat : ∃ s, (decSpec (tables vs)).pre s) :
    Verified RISCV64.target (decrypt (fnsOf vs)) (decSpec (tables vs)) :=
  ⟨code_correct hc, code_constantTime hc, hsat⟩

/-! ## A state meeting the precondition -/

/-- A state meeting decryption's contract, but for the table: a 512-bit
modulus, one-byte `e`, primes, exponents and `qInv`, an empty label, a
working space of 2080 words, the stack arguments at `sp`, and MGF1's
table's address `0x300000`. -/
def decSatState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x1800 | .a3 => 0x2000 | .a4 => 64 | .a5 => 0x3000 | .a6 => 1
    | .a7 => 0x4200 | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10000 then 1
    else bif Nat.beq a.toNat 0x10009 then 0x43 else bif Nat.beq a.toNat 0x10010 then 1
    else bif Nat.beq a.toNat 0x10019 then 0x44 else bif Nat.beq a.toNat 0x10020 then 1
    else bif Nat.beq a.toNat 0x10029 then 0x45 else bif Nat.beq a.toNat 0x10030 then 1
    else bif Nat.beq a.toNat 0x10039 then 0x46 else bif Nat.beq a.toNat 0x10040 then 1
    else bif Nat.beq a.toNat 0x10049 then 0x47 else bif Nat.beq a.toNat 0x10059 then 0x41
    else bif Nat.beq a.toNat 0x10060 then 64 else bif Nat.beq a.toNat 0x1006A then 0x02
    else bif Nat.beq a.toNat 0x10070 then 0x20 else bif Nat.beq a.toNat 0x10071 then 0x08
    else bif Nat.beq a.toNat 0x1007A then 0x30 else bif Nat.beq a.toNat 0x10082 then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x4600, 1⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x300000, 40⟩, ⟨0x300000, 40⟩, ⟨0x10000, 136⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 16640⟩]

section
variable {vs : List TVar} {w : TVar}

theorem stackArgAddr_dsat (j : Nat) (hj : j < 17) : (stackArgAddr decSatState j).toNat + 8 ≤ 0x300000 := by
  revert j; decide

theorem stackArg_dsat {j : Nat} {v : Addr} (hj : j < 17) (e : stackArg decSatState j = v) :
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) j = v :=
  (Proof.HashTable.RISCV64.withTable_below _ _ _ (stackArgAddr_dsat j hj)).trans e

theorem dsat_args :
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 0 = 1 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 1 = 0x4300 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 2 = 1 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 3 = 0x4400 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 4 = 1 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 5 = 0x4500 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 6 = 1 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 7 = 0x4600 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 8 = 1 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 9 = 0x4700 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 10 = 0 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 11 = 0x4100 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 12 = 64 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 13 = 0x20000 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 14 = 2080 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 15 = 0x300000 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 16 = 0x300000 :=
  ⟨stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide)⟩

/-- A state meeting the contract, with both tables that of `w`, at
`0x300000`. -/
theorem dec_sat (hw : w ∈ vs) (hl : (Proof.HashTable.RISCV64.names vs).length < 2 ^ 32) :
    ∃ s, (decSpec (tables vs)).pre s := by
  refine ⟨Proof.HashTable.RISCV64.withTable decSatState vs w, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ :=
    dsat_args (vs := vs) (w := w)
  have e : stackArgAddr (Proof.HashTable.RISCV64.withTable decSatState vs w) 0 = 0x10000 :=
    show stackArgAddr decSatState 0 = _ by decide
  have e3472 : stackBytes = 3471 + 1 := rfl
  unfold decSpec
  rw [e3472]
  sig_pre [Spec.RsaOaep.decryptTablesContract, Spec.RsaOaep.decryptTablesSig, Spec.RsaOaep.decryptSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argRegs, stackArgs_seventeen, List.append_eq, List.range, List.range.loop]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
    a13, a14, a15, a16, e]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact ⟨Proof.HashTable.RISCV64.tableOf w, List.mem_map_of_mem hw, Proof.HashTable.RISCV64.withTable_held _ _ _⟩
    | exact Proof.HashTable.symsOf_distinct2 hl
    | (unfold Spec.Rsa.lenValid; decide)
    | (unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords; decide)

end

end VG.Proof.RsaOaep.RISCV64.Dec
