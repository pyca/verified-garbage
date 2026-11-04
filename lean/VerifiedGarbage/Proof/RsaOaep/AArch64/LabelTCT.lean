module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelCT
public import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelT
public import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfTCT
import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelCT
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelT
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfTCT
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf

/-!
# RSAES-OAEP on AArch64: the label's hash with a table, in constant time

`hashLabelT` from two runs in the same frame and working space, with the
label at the same place and of the same length in both, the same table and
the hash function's functions at the same addresses (`LabT`): each block by
the taint analysis, each indirect call the same call (`Table.lr_tcall`), as
`hashLabel_tr`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns tcall)
open VG.Impl.Pbkdf2.Md.AArch64 (Stream Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)
open VG.Proof.RsaOaep.AArch64.Table (Tab TabAt TT initT_ok finT_ok wp_sy lr_tcall)

/-- The label, the table's address in its slot and the table, with its
functions at `ai`, `au` and `af`. -/
def LabT (G : Stream) (f : Fns) (F S lab : Addr) (labLen : Nat) (p ai au af : Addr) (W : Nat → BitVec 64)
    (t : State) : Prop :=
  LabAt t F S W lab labLen ∧ W 32 = p ∧ TT G f F S p ai au af t

variable {G : Hash} (hG : StreamOK G.stream) {f : Fns}

theorem LabT.step {F S lab : Addr} {labLen : Nat} {p ai au af : Addr} {W : Nat → BitVec 64} {t u : State}
    (h : LabT G.stream f F S lab labLen p ai au af W t) (st : Step F S [] t u) (sy : u.syms = t.syms) :
    LabT G.stream f F S lab labLen p ai au af W u :=
  ⟨h.1.congr st.rd st.wr rfl rfl, h.2.1, h.2.2.step st sy⟩

theorem LabT.congr {F S lab : Addr} {labLen : Nat} {p ai au af : Addr} {W : Nat → BitVec 64} {t u : State}
    (h : LabT G.stream f F S lab labLen p ai au af W t) (hm : u.mem = t.mem) (hs : u.syms = t.syms)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hsp : u.sp = t.sp) (hv : u.v = t.v)
    (hg : ∀ r, r ≠ .x16 → u.gpr r = t.gpr r) : LabT G.stream f F S lab labLen p ai au af W u :=
  ⟨h.1.congr hrd hwr rfl rfl, h.2.1, h.2.2.congr hm hs hrd hwr hsp hv fun r hr _ => hg r (by
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)⟩

/-- What an indirect call of the table's function needs, from `LabT`. -/
theorem labT_hv {F S lab : Addr} {labLen : Nat} {p ai au af : Addr} {Y : (Nat → BitVec 64) → State → Prop}
    {j : Nat} (hj : j < 3) {a : Addr} {n : String} {cn : Prog isa} {ts : List (String × Prog isa)}
    (hn : ∀ t, TT G.stream f F S p ai au af t → TabAt G.stream f p t → t.mem.readW (off p (8 * j)) 64 = a ∧
      t.syms n = a ∧ ts.find? (fun q => t.syms q.1 == t.syms n) = some (n, cn)) :
    ∀ W t, (LabT G.stream f F S lab labLen p ai au af W t ∧ Y W t) → W 32 = p ∧
      InRegions (t.rd ++ t.wr) (off p (8 * j)) 8 ∧ t.mem.readW (off p (8 * j)) 64 = a ∧
      ts.find? (fun q => t.syms q.1 == a) = some (n, cn) := by
  intro W t ⟨hx, _⟩
  obtain ⟨hr, hs, hf⟩ := hn t hx.2.2 hx.2.2.at
  exact ⟨hx.2.1, hx.2.2.at.rd j hj, hr, by rw [← hs]; exact hf⟩

include hG in
/-- The label's hash with the table's hash function, in two runs with the
same `LabT`. -/
theorem hashLabelT_tr {F S lab : Addr} {labLen : Nat} (hlen : labLen < 2 ^ 64) {o : Nat} (ho : o = oDig ∨ o = oLh)
    {p ai au af : Addr} :
    RelCT isa (LR F S (LabT G.stream f F S lab labLen p ai au af)) (hashLabelT f o) fun _ _ => True := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hG
  have hoo : oSt + 256 ≤ o ∧ o + 64 ≤ oW := by rcases ho with rfl | rfl <;> decide
  have hiN : ∀ t, TT G.stream f F S p ai au af t → TabAt G.stream f p t →
      t.mem.readW (off p (8 * 0)) 64 = ai ∧ t.syms G.stream.initN = ai ∧
        f.init.find? (fun q => t.syms q.1 == t.syms G.stream.initN) = some (G.stream.initN, G.stream.initC) :=
    fun t h T => ⟨T.mem.1.trans h.ai, h.ai, T.ok.i⟩
  have huN : ∀ t, TT G.stream f F S p ai au af t → TabAt G.stream f p t →
      t.mem.readW (off p (8 * 1)) 64 = au ∧ t.syms G.stream.updN = au ∧
        f.upd.find? (fun q => t.syms q.1 == t.syms G.stream.updN) = some (G.stream.updN, G.stream.updC) :=
    fun t h T => ⟨T.mem.2.1.trans h.au, h.au, T.ok.u⟩
  have hfN : ∀ t, TT G.stream f F S p ai au af t → TabAt G.stream f p t →
      t.mem.readW (off p (8 * 2)) 64 = af ∧ t.syms G.stream.finN = af ∧
        f.fin.find? (fun q => t.syms q.1 == t.syms G.stream.finN) = some (G.stream.finN, G.stream.finC) :=
    fun t h T => ⟨T.mem.2.2.trans h.af, h.af, T.ok.f⟩
  unfold hashLabelT seqs seqs seqs seqs seqs
  -- `init`.
  refine (lr_wp (X' := fun W t => LabT G.stream f F S lab labLen p ai au af W t ∧ t.gpr .x0 = off S oSt)
    (lr_taint [] (by taint_decide) nopin) fun t V W L R hx => WP.mono (wp_sy (initArgs_ok L []))
      fun u ⟨⟨Su, hm, x0⟩, sy⟩ => ⟨V, W, L.congr Su.sp Su.wr (by rw [hm]), hm ▸ R, hx.step Su sy, x0⟩).seq ?_
  refine (lr_wp (X' := LabT G.stream f F S lab labLen p ai au af) (lr_tcall 0 (labT_hv (by decide) hiN)
      (fun W t u ⟨hx, x0⟩ hm hs hrd hwr hsp hv hg => ⟨hx.congr hm hs hrd hwr hsp hv hg, (hg _ (by decide)).trans x0⟩)
      (by taint_decide) (by taint_decide) (by decide) (lr_init hG fun _ _ h => h.2))
    fun t V W L R ⟨hx, x0⟩ => WP.mono (wp_sy (initT_ok hG L R hx.2.1 hx.2.2.at x0))
      fun u ⟨⟨Lu, Su, Ru, _⟩, sy⟩ => ⟨_, W, Lu, Ru, hx.step Su sy⟩).seq ?_
  -- `update` with the label.
  refine (lr_wp (X' := fun W t => LabT G.stream f F S lab labLen p ai au af W t ∧ t.gpr .x0 = off S oSt ∧
      t.gpr .x1 = BitVec.ofNat 64 0 ∧ t.gpr .x2 = lab ∧ t.gpr .x3 = BitVec.ofNat 64 labLen ∧ t.gpr .x4 = off S oW)
    (lr_taint [] (by taint_decide) nopin)
    fun t V W L R hx => WP.mono (wp_sy (labA_ok L R hx.1 [])) fun u ⟨⟨Su, hm, x0, x1, x2, x3, x4⟩, sy⟩ =>
      ⟨V, W, L.congr Su.sp Su.wr (by rw [hm]), hm ▸ R, hx.step Su sy, x0, x1, x2, x3, x4⟩).seq ?_
  refine (lr_wp (X' := LabT G.stream f F S lab labLen p ai au af) (lr_tcall 1 (X := fun W t =>
      LabT G.stream f F S lab labLen p ai au af W t ∧ t.gpr .x0 = off S oSt ∧ t.gpr .x1 = BitVec.ofNat 64 0 ∧
        t.gpr .x2 = lab ∧ t.gpr .x3 = BitVec.ofNat 64 labLen ∧ t.gpr .x4 = off S oW) (labT_hv (by decide) huN)
      (fun W t u ⟨hx, x0, x1, x2, x3, x4⟩ hm hs hrd hwr hsp hv hg => ⟨hx.congr hm hs hrd hwr hsp hv hg,
        (hg _ (by decide)).trans x0, (hg _ (by decide)).trans x1, (hg _ (by decide)).trans x2,
        (hg _ (by decide)).trans x3, (hg _ (by decide)).trans x4⟩)
      (by taint_decide) (by taint_decide) (by decide)
      (lr_updExt hG (BitVec.ofNat 64 0) (len := labLen) (d := lab) hlen fun _ _ ⟨⟨A, _⟩, x0, x1, x2, x3, x4⟩ =>
        ⟨⟨A.cov, A.dS, A.dK⟩, x0, x1, x2, x3, x4⟩))
    fun t V W L R ⟨hx, x0, x1, x2, x3, x4⟩ => WP.mono (wp_sy (updExtT_ok hG L R hx.2.1 hx.2.2.at hx.1.len
      hx.1.cov hx.1.dS hx.1.dK x0 x2 x3 x4)) fun u ⟨⟨Lu, Su, Ru, _⟩, sy⟩ => ⟨_, W, Lu, Ru, hx.step Su sy⟩).seq ?_
  -- `finalize`.
  refine (lr_wp (X' := fun W t => LabT G.stream f F S lab labLen p ai au af W t ∧ t.gpr .x0 = off S oSt ∧
      t.gpr .x1 = BitVec.ofNat 64 labLen ∧ t.gpr .x2 = off S o ∧ t.gpr .x3 = off S oW)
    (lr_taint [] (check_of_zImm (τ := Taint.ofRegs [])
      (c := .block (scr .x0 oSt ++ ([.ldrSp .x1 sLabLen] : List Instr) ++ scr .x2 o ++ scr .x3 oW))
      (c' := .block (scr .x0 oSt ++ ([.ldrSp .x1 sLabLen] : List Instr) ++ scr .x2 0 ++ scr .x3 oW)) rfl
      (by taint_decide)) nopin)
    fun t V W L R hx => WP.mono (wp_sy (labF_ok L R hx.1.hll (o := o) (by rcases ho with rfl | rfl <;> decide) []))
      fun u ⟨⟨Su, hm, x0, x1, x2, x3⟩, sy⟩ =>
        ⟨V, W, L.congr Su.sp Su.wr (by rw [hm]), hm ▸ R, hx.step Su sy, x0, x1, x2, x3⟩).seq ?_
  exact lr_tcall 2 (labT_hv (by decide) hfN) (fun W t u ⟨hx, x0, x1, x2, x3⟩ hm hs hrd hwr hsp hv hg =>
      ⟨hx.congr hm hs hrd hwr hsp hv hg, (hg _ (by decide)).trans x0, (hg _ (by decide)).trans x1,
        (hg _ (by decide)).trans x2, (hg _ (by decide)).trans x3⟩)
    (by taint_decide) (by taint_decide) (by decide)
    (lr_fin hG (BitVec.ofNat 64 labLen) (.inr hoo) fun _ _ h => h.2)

end VG.Proof.RsaOaep.AArch64
