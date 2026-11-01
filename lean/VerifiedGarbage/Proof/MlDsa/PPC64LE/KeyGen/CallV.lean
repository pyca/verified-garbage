module

import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.CallSP
import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.ContractsV
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Call
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# ML-DSA on PPC64LE: calling the primitives only verification and signing use

As `ip_ok` and `ip_tr` (`Call.lean`), in the buffers of a `Site`:
`vg_mldsa_sub`, `vg_mldsa_hint_bit_unpack`, `vg_mldsa_bit_unpack`,
`vg_mldsa_sample_in_ball`, `vg_mldsa_norm_lt`, `vg_mldsa_use_hint` and
`vg_mldsa_unpack_t1`. An integer argument is moved to the whole register: a
`usize` is all of it (`imm_toNat`), a `u32` its low word (`imm32`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.KeyGen

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Impl.MlDsa.PPC64LE.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `vg_mldsa_sub` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {f g : Ptr}

theorem sub_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : AddOk L Wb f g)
    (rf : Reduced s.mem (lpa L f)) (rg : Reduced s.mem (lpa L g)) :
    (subContract PPC64LE.abi stk).pre (view (glueSt s (addArgs f g)) (addRd L g) (addWr L f)) := by
  have hsp := view_glue_sp s (addArgs f g) (addRd L g) (addWr L f)
  obtain ⟨g3, g4⟩ := add_vg hs m (addRd L g) (addWr L f)
  refine sub_pre g3 g4 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.dE m.d (.inl m.wf))
    (hs.kE m.pf hstk hsp) (hs.kE m.pg hstk hsp) (hs.fitE m.pf (by decide)) (hs.fitE m.pg (by decide)) ?_ ?_
  · rw [view_glue_mem]; exact rf
  · rw [view_glue_mem]; exact rg

theorem sub_ok {c : Prog isa} (hc : Callee c (fun stk => subContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : AddOk L Wb f g)
    (rf : Reduced s.mem (lpa L f)) (rg : Reduced s.mem (lpa L g)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri f 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (lpa L f) (sub (polyAt s.mem (lpa L f)) (polyAt s.mem (lpa L g))) → Q s') :
    WP isa (callAt name c (addArgs f g)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := add_cov hs m
  refine callV hver.1 (hs.depth hc.stack hS) m.hg (sub_preS hs (Nat.le_trans hstk hS) m rf rg) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri f 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g3, g4⟩ := add_vg hs m (addRd L g) (addWr L f)
  have := sub_post hp
  rwa [State.withRegions_mem, g3, g4, view_glue_mem] at this

theorem sub_tr {c : Prog isa} (hc : Callee c (fun stk => subContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : AddOk L Wb f g) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧
      Reduced x.mem (lpa L f) ∧ Reduced x.mem (lpa L g) ∧ Reduced y.mem (lpa L f) ∧ Reduced y.mem (lpa L g)) :
    RelCT isa P (callAt name c (addArgs f g)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rxf, rxg, ryf, ryg⟩ := hP x y hxy
  obtain ⟨gx3, gx4⟩ := add_vg hx m (addRd L g) (addWr L f)
  obtain ⟨gy3, gy4⟩ := add_vg hy m (addRd L g) (addWr L f)
  exact ⟨addRd L g, addWr L f, sub_preS hx (Nat.le_trans hstk hS) m rxf rxg, sub_preS hy (Nat.le_trans hstk hS) m ryf ryg,
    sub_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]),
    (add_cov hx m).1, (add_cov hx m).2, (add_cov hy m).1, (add_cov hy m).2⟩

end

/-! ## `vg_mldsa_hint_bit_unpack` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {y h : Ptr} {len om hl : Nat}

abbrev hbuArgs (y : Ptr) (len om : Nat) (h : Ptr) (hl : Nat) : List (Reg × Arg) :=
  [(.r3, .ptr y), (.r4, .imm len), (.r5, .imm om), (.r6, .ptr h), (.r7, .imm hl)]
abbrev hbuRd (L : Lay) (y : Ptr) (len : Nat) : List Region := [L.R (ix y.1) y.2 len]
abbrev hbuWr (L : Lay) (h : Ptr) (hl : Nat) : List Region := [L.R (ix h.1) h.2 (hl * 4)]

/-- The facts `vg_mldsa_hint_bit_unpack` needs of its arguments. -/
structure HbuOk (L : Lay) (Wb : List Nat) (y : Ptr) (len om : Nat) (h : Ptr) (hl : Nat) : Prop where
  py : PtrIn L y len
  ph : PtrIn L h (hl * 4)
  wh : ix h.1 ∈ Wb
  d1 : sepB L.sizes (tri y len) (tri h (hl * 4)) = true
  hp : (om, len - om) ∈ hintParams
  ho : om ≤ len
  hh : hl = 256 * (len - om)
  lt : 0 < len ∧ len < 2 ^ 31 ∧ om < 2 ^ 31 ∧ 0 < hl * 4 ∧ hl < 2 ^ 31

theorem HbuOk.hg (m : HbuOk L Wb y len om h hl) : glueOk (hbuArgs y len om h hl) = true := by
  obtain ⟨-, l1, l2, -, l4⟩ := m.lt
  have h1 : argOk (.imm len) = true := argOk_imm l1
  have h2 : argOk (.imm om) = true := argOk_imm l2
  have h3 : argOk (.imm hl) = true := argOk_imm l4
  simp [glueOk, argReg, m.py.1, m.ph.1, h1, h2, h3]

theorem hbuArgs_nodup : ((hbuArgs y len om h hl).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem hbu_vg {s : State} (hs : Site L Wb STK s) (m : HbuOk L Wb y len om h hl) (rd wr : List Region) :
    (view (glueSt s (hbuArgs y len om h hl)) rd wr).gpr .r3 = lpa L y ∧
    (view (glueSt s (hbuArgs y len om h hl)) rd wr).gpr .r4 = BitVec.ofNat 64 len ∧
    (view (glueSt s (hbuArgs y len om h hl)) rd wr).gpr .r5 = BitVec.ofNat 64 om ∧
    (view (glueSt s (hbuArgs y len om h hl)) rd wr).gpr .r6 = lpa L h ∧
    (view (glueSt s (hbuArgs y len om h hl)) rd wr).gpr .r7 = BitVec.ofNat 64 hl :=
  ⟨hs.vG m.hg hbuArgs_nodup (by simp) m.py.1 (by decide) _ _, vI m.hg hbuArgs_nodup (by simp) (by decide) _ _,
    vI m.hg hbuArgs_nodup (by simp) (by decide) _ _, hs.vG m.hg hbuArgs_nodup (by simp) m.ph.1 (by decide) _ _,
    vI m.hg hbuArgs_nodup (by simp) (by decide) _ _⟩

theorem hbu_cov {s : State} (hs : Site L Wb STK s) (m : HbuOk L Wb y len om h hl) :
    Covers (hbuRd L y len ++ hbuWr L h hl) (s.rd ++ s.wr) ∧ Covers (hbuWr L h hl) s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE m.py) Covers.nil) (Covers.right (Covers.cons (hs.cwE m.ph m.wh) Covers.nil)),
    Covers.cons (hs.cwE m.ph m.wh) Covers.nil⟩

theorem hbu_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : HbuOk L Wb y len om h hl) :
    (hintBitUnpackContract PPC64LE.abi stk).pre
      (view (glueSt s (hbuArgs y len om h hl)) (hbuRd L y len) (hbuWr L h hl)) := by
  have hsp := view_glue_sp s (hbuArgs y len om h hl) (hbuRd L y len) (hbuWr L h hl)
  obtain ⟨g3, g4, g5, g6, g7⟩ := hbu_vg hs m (hbuRd L y len) (hbuWr L h hl)
  obtain ⟨l0, ll, lo, h0, lh⟩ := m.lt
  have e5 : ((view (glueSt s (hbuArgs y len om h hl)) (hbuRd L y len) (hbuWr L h hl)).gpr .r5).setWidth 32 =
      BitVec.ofNat 32 om := by
    rw [g5]; exact imm32 (by omega_arith)
  refine hbu_pre g3 g4 e5 g6 g7 (by rw [State.withRegions_rd, imm_toNat (by omega_arith)])
    (by rw [State.withRegions_wr, imm_toNat (by omega_arith)]) (by rw [hsp]; exact Nat.le_trans hstk hs.spk) ?_ ?_ ?_
    (by rw [imm_toNat (by omega_arith)]; exact hs.fitE m.py l0) (by rw [imm_toNat (by omega_arith)]; exact hs.fitE m.ph h0)
    (by rw [imm32_toNat (by omega_arith), imm_toNat (by omega_arith)]; exact m.hp)
    (by rw [imm32_toNat (by omega_arith), imm_toNat (by omega_arith)]; exact m.ho)
    (by rw [imm32_toNat (by omega_arith), imm_toNat (by omega_arith), imm_toNat (by omega_arith)]; exact m.hh)
  · rw [imm_toNat (by omega_arith), imm_toNat (by omega_arith)]; exact hs.dE m.d1 (.inr m.wh)
  · rw [imm_toNat (by omega_arith)]; exact hs.kE m.py hstk hsp
  · rw [imm_toNat (by omega_arith)]; exact hs.kE m.ph hstk hsp

theorem hbu_ok {c : Prog isa} (hc : Callee c (fun stk => hintBitUnpackContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : HbuOk L Wb y len om h hl) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri h (hl * 4), (1, 0, STK)]) s s' →
      (match hintBitUnpack om (len - om) (bytesAt s.mem (lpa L y) len) with
        | some hint => (s'.gpr .r3).setWidth 32 = 1 ∧ HintIs s'.mem (lpa L h) (len - om) hint
        | none => (s'.gpr .r3).setWidth 32 = 0) → Q s') :
    WP isa (callAt name c (hbuArgs y len om h hl)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := hbu_cov hs m
  obtain ⟨l0, ll, lo, h0, lh⟩ := m.lt
  refine callV hver.1 (hs.depth hc.stack hS) m.hg (hbu_preS hs (Nat.le_trans hstk hS) m) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri h (hl * 4)] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g3, g4, g5, g6, -⟩ := hbu_vg hs m (hbuRd L y len) (hbuWr L h hl)
  have := hbu_post hp
  rwa [g3, g4, g5, g6, view_glue_mem, State.withRegions_mem, State.withRegions_gpr, imm32 (by omega_arith),
    imm32_toNat (by omega_arith), imm_toNat (by omega_arith)] at this

theorem hbu_tr {c : Prog isa} (hc : Callee c (fun stk => hintBitUnpackContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : HbuOk L Wb y len om h hl) {P : State → State → Prop}
    (hP : ∀ x y', P x y' → Site L Wb STK x ∧ Site L Wb STK y' ∧ x.sp = y'.sp ∧
      bytesAt x.mem (lpa L y) len = bytesAt y'.mem (lpa L y) len) :
    RelCT isa P (callAt name c (hbuArgs y len om h hl)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨l0, ll, lo, h0, lh⟩ := m.lt
  refine callV_tr hver.1 hver.2.1 m.hg fun x y' hxy => ?_
  obtain ⟨hx, hy, hsp, hl'⟩ := hP x y' hxy
  obtain ⟨gx3, gx4, gx5, gx6, gx7⟩ := hbu_vg hx m (hbuRd L y len) (hbuWr L h hl)
  obtain ⟨gy3, gy4, gy5, gy6, gy7⟩ := hbu_vg hy m (hbuRd L y len) (hbuWr L h hl)
  refine ⟨hbuRd L y len, hbuWr L h hl, hbu_preS hx (Nat.le_trans hstk hS) m, hbu_preS hy (Nat.le_trans hstk hS) m,
    hbu_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]) (by rw [gx5, gy5])
      (by rw [gx6, gy6]) (by rw [gx7, gy7]) ?_, (hbu_cov hx m).1, (hbu_cov hx m).2, (hbu_cov hy m).1,
    (hbu_cov hy m).2⟩
  rw [gx3, gy3, gx4, gy4, view_glue_mem, view_glue_mem, imm_toNat (by omega_arith)]
  exact hl'

end

/-! ## `vg_mldsa_bit_unpack` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {v f : Ptr} {len a b : Nat}

abbrev buArgs (v : Ptr) (len a b : Nat) (f : Ptr) : List (Reg × Arg) :=
  [(.r3, .ptr v), (.r4, .imm len), (.r5, .imm a), (.r6, .imm b), (.r7, .ptr f)]
abbrev buRd (L : Lay) (v : Ptr) (len : Nat) : List Region := [L.R (ix v.1) v.2 len]
abbrev buWr (L : Lay) (f : Ptr) : List Region := [L.R (ix f.1) f.2 1024]

/-- The facts `vg_mldsa_bit_unpack` needs of its arguments. -/
structure BuOk (L : Lay) (Wb : List Nat) (v : Ptr) (len a b : Nat) (f : Ptr) : Prop where
  pv : PtrIn L v len
  pf : PtrIn L f 1024
  wf : ix f.1 ∈ Wb
  d1 : sepB L.sizes (tri v len) (tri f 1024) = true
  hab : (a, b) ∈ bitPackParams
  hl : len = 32 * bitlen (a + b)
  lt : 0 < len ∧ len < 2 ^ 31 ∧ a < 2 ^ 31 ∧ b < 2 ^ 31

theorem BuOk.hg (m : BuOk L Wb v len a b f) : glueOk (buArgs v len a b f) = true := by
  obtain ⟨-, l1, l2, l3⟩ := m.lt
  have h1 : argOk (.imm len) = true := argOk_imm l1
  have h2 : argOk (.imm a) = true := argOk_imm l2
  have h3 : argOk (.imm b) = true := argOk_imm l3
  simp [glueOk, argReg, m.pv.1, m.pf.1, h1, h2, h3]

theorem buArgs_nodup : ((buArgs v len a b f).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem bu_vg {s : State} (hs : Site L Wb STK s) (m : BuOk L Wb v len a b f) (rd wr : List Region) :
    (view (glueSt s (buArgs v len a b f)) rd wr).gpr .r3 = lpa L v ∧
    (view (glueSt s (buArgs v len a b f)) rd wr).gpr .r4 = BitVec.ofNat 64 len ∧
    (view (glueSt s (buArgs v len a b f)) rd wr).gpr .r5 = BitVec.ofNat 64 a ∧
    (view (glueSt s (buArgs v len a b f)) rd wr).gpr .r6 = BitVec.ofNat 64 b ∧
    (view (glueSt s (buArgs v len a b f)) rd wr).gpr .r7 = lpa L f :=
  ⟨hs.vG m.hg buArgs_nodup (by simp) m.pv.1 (by decide) _ _, vI m.hg buArgs_nodup (by simp) (by decide) _ _,
    vI m.hg buArgs_nodup (by simp) (by decide) _ _, vI m.hg buArgs_nodup (by simp) (by decide) _ _,
    hs.vG m.hg buArgs_nodup (by simp) m.pf.1 (by decide) _ _⟩

theorem bu_cov {s : State} (hs : Site L Wb STK s) (m : BuOk L Wb v len a b f) :
    Covers (buRd L v len ++ buWr L f) (s.rd ++ s.wr) ∧ Covers (buWr L f) s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE m.pv) Covers.nil) (Covers.right (Covers.cons (hs.cwE m.pf m.wf) Covers.nil)),
    Covers.cons (hs.cwE m.pf m.wf) Covers.nil⟩

theorem bu_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : BuOk L Wb v len a b f) :
    (bitUnpackContract PPC64LE.abi stk).pre (view (glueSt s (buArgs v len a b f)) (buRd L v len) (buWr L f)) := by
  have hsp := view_glue_sp s (buArgs v len a b f) (buRd L v len) (buWr L f)
  obtain ⟨g3, g4, g5, g6, g7⟩ := bu_vg hs m (buRd L v len) (buWr L f)
  obtain ⟨l0, ll, la, lb⟩ := m.lt
  have e5 : ((view (glueSt s (buArgs v len a b f)) (buRd L v len) (buWr L f)).gpr .r5).setWidth 32 =
      BitVec.ofNat 32 a := by
    rw [g5]; exact imm32 (by omega_arith)
  have e6 : ((view (glueSt s (buArgs v len a b f)) (buRd L v len) (buWr L f)).gpr .r6).setWidth 32 =
      BitVec.ofNat 32 b := by
    rw [g6]; exact imm32 (by omega_arith)
  refine bu_pre g3 g4 e5 e6 g7 (by rw [State.withRegions_rd, imm_toNat (by omega_arith)]) rfl
    (by rw [hsp]; exact Nat.le_trans hstk hs.spk) ?_ ?_ (hs.kE m.pf hstk hsp)
    (by rw [imm_toNat (by omega_arith)]; exact hs.fitE m.pv l0) (hs.fitE m.pf (by decide))
    (by rw [imm32_toNat (by omega_arith), imm32_toNat (by omega_arith)]; exact m.hab)
    (by rw [imm_toNat (by omega_arith), imm32_toNat (by omega_arith), imm32_toNat (by omega_arith)]; exact m.hl)
  · rw [imm_toNat (by omega_arith)]; exact hs.dE m.d1 (.inr m.wf)
  · rw [imm_toNat (by omega_arith)]; exact hs.kE m.pv hstk hsp

theorem bu_ok {c : Prog isa} (hc : Callee c (fun stk => bitUnpackContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : BuOk L Wb v len a b f) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri f 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (lpa L f) (toRq (bitUnpack (bytesAt s.mem (lpa L v) len) a b)) → Q s') :
    WP isa (callAt name c (buArgs v len a b f)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := bu_cov hs m
  obtain ⟨l0, ll, la, lb⟩ := m.lt
  refine callV hver.1 (hs.depth hc.stack hS) m.hg (bu_preS hs (Nat.le_trans hstk hS) m) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri f 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g3, g4, g5, g6, g7⟩ := bu_vg hs m (buRd L v len) (buWr L f)
  have := bu_post hp
  rwa [State.withRegions_mem, g3, g4, g5, g6, g7, view_glue_mem, imm32 (by omega_arith), imm32 (by omega_arith),
    imm32_toNat (by omega_arith), imm32_toNat (by omega_arith), imm_toNat (by omega_arith)] at this

theorem bu_tr {c : Prog isa} (hc : Callee c (fun stk => bitUnpackContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : BuOk L Wb v len a b f) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp) :
    RelCT isa P (callAt name c (buArgs v len a b f)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp⟩ := hP x y hxy
  obtain ⟨gx3, gx4, gx5, gx6, gx7⟩ := bu_vg hx m (buRd L v len) (buWr L f)
  obtain ⟨gy3, gy4, gy5, gy6, gy7⟩ := bu_vg hy m (buRd L v len) (buWr L f)
  exact ⟨buRd L v len, buWr L f, bu_preS hx (Nat.le_trans hstk hS) m, bu_preS hy (Nat.le_trans hstk hS) m,
    bu_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]) (by rw [gx5, gy5])
      (by rw [gx6, gy6]) (by rw [gx7, gy7]), (bu_cov hx m).1, (bu_cov hx m).2, (bu_cov hy m).1, (bu_cov hy m).2⟩

end

/-! ## `vg_mldsa_sample_in_ball` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {ct c w : Ptr} {len tau : Nat}

abbrev ballArgs (ct : Ptr) (len tau : Nat) (c w : Ptr) : List (Reg × Arg) :=
  [(.r3, .ptr ct), (.r4, .imm len), (.r5, .imm tau), (.r6, .ptr c), (.r7, .ptr w)]
abbrev ballRd (L : Lay) (ct : Ptr) (len : Nat) : List Region := [L.R (ix ct.1) ct.2 len]
abbrev ballWr (L : Lay) (c w : Ptr) : List Region := [L.R (ix c.1) c.2 1024, L.R (ix w.1) w.2 2048]

/-- The facts `vg_mldsa_sample_in_ball` needs of its arguments. -/
structure BallOk (L : Lay) (Wb : List Nat) (ct : Ptr) (len tau : Nat) (c w : Ptr) : Prop where
  pct : PtrIn L ct len
  pc : PtrIn L c 1024
  pw : PtrIn L w 2048
  wc : ix c.1 ∈ Wb
  ww : ix w.1 ∈ Wb
  d1 : sepB L.sizes (tri ct len) (tri c 1024) = true
  d2 : sepB L.sizes (tri ct len) (tri w 2048) = true
  d3 : sepB L.sizes (tri c 1024) (tri w 2048) = true
  hp : (len, tau) ∈ ballParams
  lt : 0 < len ∧ len < 2 ^ 31 ∧ tau < 2 ^ 31

theorem BallOk.hg (m : BallOk L Wb ct len tau c w) : glueOk (ballArgs ct len tau c w) = true := by
  obtain ⟨-, l1, l2⟩ := m.lt
  have h1 : argOk (.imm len) = true := argOk_imm l1
  have h2 : argOk (.imm tau) = true := argOk_imm l2
  simp [glueOk, argReg, m.pct.1, m.pc.1, m.pw.1, h1, h2]

theorem ballArgs_nodup : ((ballArgs ct len tau c w).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem ball_vg {s : State} (hs : Site L Wb STK s) (m : BallOk L Wb ct len tau c w) (rd wr : List Region) :
    (view (glueSt s (ballArgs ct len tau c w)) rd wr).gpr .r3 = lpa L ct ∧
    (view (glueSt s (ballArgs ct len tau c w)) rd wr).gpr .r4 = BitVec.ofNat 64 len ∧
    (view (glueSt s (ballArgs ct len tau c w)) rd wr).gpr .r5 = BitVec.ofNat 64 tau ∧
    (view (glueSt s (ballArgs ct len tau c w)) rd wr).gpr .r6 = lpa L c ∧
    (view (glueSt s (ballArgs ct len tau c w)) rd wr).gpr .r7 = lpa L w :=
  ⟨hs.vG m.hg ballArgs_nodup (by simp) m.pct.1 (by decide) _ _, vI m.hg ballArgs_nodup (by simp) (by decide) _ _,
    vI m.hg ballArgs_nodup (by simp) (by decide) _ _, hs.vG m.hg ballArgs_nodup (by simp) m.pc.1 (by decide) _ _,
    hs.vG m.hg ballArgs_nodup (by simp) m.pw.1 (by decide) _ _⟩

theorem ball_cov {s : State} (hs : Site L Wb STK s) (m : BallOk L Wb ct len tau c w) :
    Covers (ballRd L ct len ++ ballWr L c w) (s.rd ++ s.wr) ∧ Covers (ballWr L c w) s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE m.pct) Covers.nil)
    (Covers.right (Covers.cons (hs.cwE m.pc m.wc) (Covers.cons (hs.cwE m.pw m.ww) Covers.nil))),
    Covers.cons (hs.cwE m.pc m.wc) (Covers.cons (hs.cwE m.pw m.ww) Covers.nil)⟩

theorem ball_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK)
    (m : BallOk L Wb ct len tau c w) :
    (sampleInBallContract PPC64LE.abi stk).pre
      (view (glueSt s (ballArgs ct len tau c w)) (ballRd L ct len) (ballWr L c w)) := by
  have hsp := view_glue_sp s (ballArgs ct len tau c w) (ballRd L ct len) (ballWr L c w)
  obtain ⟨g3, g4, g5, g6, g7⟩ := ball_vg hs m (ballRd L ct len) (ballWr L c w)
  obtain ⟨l0, ll, lt⟩ := m.lt
  have e5 : ((view (glueSt s (ballArgs ct len tau c w)) (ballRd L ct len) (ballWr L c w)).gpr .r5).setWidth 32 =
      BitVec.ofNat 32 tau := by
    rw [g5]; exact imm32 (by omega_arith)
  refine ball_pre g3 g4 e5 g6 g7 (by rw [State.withRegions_rd, imm_toNat (by omega_arith)]) rfl
    (by rw [hsp]; exact Nat.le_trans hstk hs.spk) ?_ ?_ (hs.dE m.d3 (.inl m.wc)) ?_ (hs.kE m.pc hstk hsp)
    (hs.kE m.pw hstk hsp) (by rw [imm_toNat (by omega_arith)]; exact hs.fitE m.pct l0) (hs.fitE m.pc (by decide))
    (hs.fitE m.pw (by decide)) (by rw [imm_toNat (by omega_arith), imm32_toNat (by omega_arith)]; exact m.hp)
  · rw [imm_toNat (by omega_arith)]; exact hs.dE m.d1 (.inr m.wc)
  · rw [imm_toNat (by omega_arith)]; exact hs.dE m.d2 (.inr m.ww)
  · rw [imm_toNat (by omega_arith)]; exact hs.kE m.pct hstk hsp

theorem ball_ok {cd : Prog isa} (hc : Callee cd (fun stk => sampleInBallContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : BallOk L Wb ct len tau c w) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri c 1024, tri w 2048, (1, 0, STK)]) s s' →
      ((s'.gpr .r3).setWidth 32 = 1 → Reduced s'.mem (lpa L c)) →
      Outcome (fun b => (sampleInBall tau b.ball (bytesAt s.mem (lpa L ct) len)).map toRq) ((s'.gpr .r3).setWidth 32)
        (polyAt s'.mem (lpa L c)) → Q s') :
    WP isa (callAt name cd (ballArgs ct len tau c w)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := ball_cov hs m
  obtain ⟨l0, ll, lt⟩ := m.lt
  refine callV hver.1 (hs.depth hc.stack hS) m.hg (ball_preS hs (Nat.le_trans hstk hS) m) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri c 1024, tri w 2048] (Nat.le_trans hc.stack hS) hk) ?_ ?_
  all_goals
    obtain ⟨g3, g4, g5, g6, -⟩ := ball_vg hs m (ballRd L ct len) (ballWr L c w)
    have := ball_post hp
    rw [State.withRegions_mem, State.withRegions_gpr, g3, g4, g5, g6, view_glue_mem, imm32 (by omega_arith),
      imm32_toNat (by omega_arith), imm_toNat (by omega_arith)] at this
  exacts [this.1, this.2]

theorem ball_tr {cd : Prog isa} (hc : Callee cd (fun stk => sampleInBallContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : BallOk L Wb ct len tau c w) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧
      bytesAt x.mem (lpa L ct) len = bytesAt y.mem (lpa L ct) len) :
    RelCT isa P (callAt name cd (ballArgs ct len tau c w)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨l0, ll, lt⟩ := m.lt
  refine callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, hl⟩ := hP x y hxy
  obtain ⟨gx3, gx4, gx5, gx6, gx7⟩ := ball_vg hx m (ballRd L ct len) (ballWr L c w)
  obtain ⟨gy3, gy4, gy5, gy6, gy7⟩ := ball_vg hy m (ballRd L ct len) (ballWr L c w)
  refine ⟨ballRd L ct len, ballWr L c w, ball_preS hx (Nat.le_trans hstk hS) m, ball_preS hy (Nat.le_trans hstk hS) m,
    ball_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]) (by rw [gx5, gy5])
      (by rw [gx6, gy6]) (by rw [gx7, gy7]) ?_, (ball_cov hx m).1, (ball_cov hx m).2, (ball_cov hy m).1,
    (ball_cov hy m).2⟩
  rw [gx3, gy3, gx4, gy4, view_glue_mem, view_glue_mem, imm_toNat (by omega_arith)]
  exact hl

end

/-! ## `vg_mldsa_norm_lt` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {f : Ptr} {bd : Nat}

abbrev nlArgs (f : Ptr) (bd : Nat) : List (Reg × Arg) := [(.r3, .ptr f), (.r4, .imm bd)]

theorem nl_hg (pf : PtrIn L f 1024) (hbd : bd < 2 ^ 31) : glueOk (nlArgs f bd) = true := by
  have h1 : argOk (.imm bd) = true := argOk_imm hbd
  simp [glueOk, argReg, pf.1, h1]

theorem nlArgs_nodup : ((nlArgs f bd).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide

theorem nl_vg {s : State} (hs : Site L Wb STK s) (pf : PtrIn L f 1024) (hbd : bd < 2 ^ 31) (rd wr : List Region) :
    (view (glueSt s (nlArgs f bd)) rd wr).gpr .r3 = lpa L f ∧
    (view (glueSt s (nlArgs f bd)) rd wr).gpr .r4 = BitVec.ofNat 64 bd :=
  ⟨hs.vG (nl_hg pf hbd) nlArgs_nodup (by simp) pf.1 (by decide) _ _,
    vI (nl_hg pf hbd) nlArgs_nodup (by simp) (by decide) _ _⟩

theorem nl_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (pf : PtrIn L f 1024)
    (hbd : bd < 2 ^ 31) (hr : Reduced s.mem (lpa L f)) :
    (normLtContract PPC64LE.abi stk).pre (view (glueSt s (nlArgs f bd)) [L.R (ix f.1) f.2 1024] []) := by
  have hsp := view_glue_sp s (nlArgs f bd) [L.R (ix f.1) f.2 1024] []
  obtain ⟨g3, -⟩ := nl_vg hs pf hbd [L.R (ix f.1) f.2 1024] []
  refine normLt_pre g3 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.kE pf hstk hsp)
    (hs.fitE pf (by decide)) ?_
  rw [view_glue_mem]; exact hr

theorem nl_cov {s : State} (hs : Site L Wb STK s) (pf : PtrIn L f 1024) :
    Covers ([L.R (ix f.1) f.2 1024] ++ []) (s.rd ++ s.wr) ∧ Covers [] s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE pf) Covers.nil) Covers.nil, Covers.nil⟩

theorem nl_ok {c : Prog isa} (hc : Callee c (fun stk => normLtContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (pf : PtrIn L f 1024) (hbd : bd < 2 ^ 31)
    (hr : Reduced s.mem (lpa L f)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(1, 0, STK)]) s s' →
      (s'.gpr .r3).setWidth 32 = (if normRq [polyAt s.mem (lpa L f)] < bd then 1 else 0) → Q s') :
    WP isa (callAt name c (nlArgs f bd)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := nl_cov hs pf
  refine callV hver.1 (hs.depth hc.stack hS) (nl_hg pf hbd) (nl_preS hs (Nat.le_trans hstk hS) pf hbd hr) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g3, g4⟩ := nl_vg hs pf hbd [L.R (ix f.1) f.2 1024] []
  have := normLt_post hp
  rwa [g3, g4, view_glue_mem, State.withRegions_gpr, imm32 (by omega_arith), imm32_toNat (by omega_arith)] at this

theorem nl_tr {c : Prog isa} (hc : Callee c (fun stk => normLtContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (pf : PtrIn L f 1024) (hbd : bd < 2 ^ 31) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L f) ∧
      Reduced y.mem (lpa L f)) :
    RelCT isa P (callAt name c (nlArgs f bd)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 (nl_hg pf hbd) fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rx, ry⟩ := hP x y hxy
  obtain ⟨gx3, gx4⟩ := nl_vg hx pf hbd [L.R (ix f.1) f.2 1024] []
  obtain ⟨gy3, gy4⟩ := nl_vg hy pf hbd [L.R (ix f.1) f.2 1024] []
  exact ⟨_, _, nl_preS hx (Nat.le_trans hstk hS) pf hbd rx, nl_preS hy (Nat.le_trans hstk hS) pf hbd ry,
    normLt_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]),
    (nl_cov hx pf).1, (nl_cov hx pf).2, (nl_cov hy pf).1, (nl_cov hy pf).2⟩

end

/-! ## `vg_mldsa_use_hint` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {h r o : Ptr} {g2 : Nat}

abbrev uhArgs (h r : Ptr) (g2 : Nat) (o : Ptr) : List (Reg × Arg) :=
  [(.r3, .ptr h), (.r4, .ptr r), (.r5, .imm g2), (.r6, .ptr o)]
abbrev uhRd (L : Lay) (h r : Ptr) : List Region := [L.R (ix h.1) h.2 1024, L.R (ix r.1) r.2 1024]
abbrev uhWr (L : Lay) (o : Ptr) : List Region := [L.R (ix o.1) o.2 1024]

/-- The facts `vg_mldsa_use_hint` needs of its arguments. -/
structure UhOk (L : Lay) (Wb : List Nat) (h r : Ptr) (g2 : Nat) (o : Ptr) : Prop where
  ph : PtrIn L h 1024
  pr : PtrIn L r 1024
  po : PtrIn L o 1024
  wo : ix o.1 ∈ Wb
  d1 : sepB L.sizes (tri h 1024) (tri o 1024) = true
  d2 : sepB L.sizes (tri r 1024) (tri o 1024) = true
  hg : g2 ∈ gamma2s
  lt : g2 < 2 ^ 31

theorem UhOk.hg' (m : UhOk L Wb h r g2 o) : glueOk (uhArgs h r g2 o) = true := by
  have h1 : argOk (.imm g2) = true := argOk_imm m.lt
  simp [glueOk, argReg, m.ph.1, m.pr.1, m.po.1, h1]

theorem uhArgs_nodup : ((uhArgs h r g2 o).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide

theorem uh_vg {s : State} (hs : Site L Wb STK s) (m : UhOk L Wb h r g2 o) (rd wr : List Region) :
    (view (glueSt s (uhArgs h r g2 o)) rd wr).gpr .r3 = lpa L h ∧
    (view (glueSt s (uhArgs h r g2 o)) rd wr).gpr .r4 = lpa L r ∧
    (view (glueSt s (uhArgs h r g2 o)) rd wr).gpr .r5 = BitVec.ofNat 64 g2 ∧
    (view (glueSt s (uhArgs h r g2 o)) rd wr).gpr .r6 = lpa L o :=
  ⟨hs.vG m.hg' uhArgs_nodup (by simp) m.ph.1 (by decide) _ _, hs.vG m.hg' uhArgs_nodup (by simp) m.pr.1 (by decide) _ _,
    vI m.hg' uhArgs_nodup (by simp) (by decide) _ _, hs.vG m.hg' uhArgs_nodup (by simp) m.po.1 (by decide) _ _⟩

theorem uh_cov {s : State} (hs : Site L Wb STK s) (m : UhOk L Wb h r g2 o) :
    Covers (uhRd L h r ++ uhWr L o) (s.rd ++ s.wr) ∧ Covers (uhWr L o) s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE m.ph) (Covers.cons (hs.crE m.pr) Covers.nil))
    (Covers.right (Covers.cons (hs.cwE m.po m.wo) Covers.nil)), Covers.cons (hs.cwE m.po m.wo) Covers.nil⟩

theorem uh_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : UhOk L Wb h r g2 o)
    (hr : Reduced s.mem (lpa L r)) :
    (useHintContract PPC64LE.abi stk).pre (view (glueSt s (uhArgs h r g2 o)) (uhRd L h r) (uhWr L o)) := by
  have hsp := view_glue_sp s (uhArgs h r g2 o) (uhRd L h r) (uhWr L o)
  obtain ⟨g3, g4, g5, g6⟩ := uh_vg hs m (uhRd L h r) (uhWr L o)
  have e5 : ((view (glueSt s (uhArgs h r g2 o)) (uhRd L h r) (uhWr L o)).gpr .r5).setWidth 32 =
      BitVec.ofNat 32 g2 := by
    rw [g5]; exact imm32 (by have := m.lt; omega_arith)
  refine useHint_pre g3 g4 e5 g6 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk)
    (hs.dE m.d1 (.inr m.wo)) (hs.dE m.d2 (.inr m.wo)) (hs.kE m.ph hstk hsp) (hs.kE m.pr hstk hsp)
    (hs.kE m.po hstk hsp) (hs.fitE m.ph (by decide)) (hs.fitE m.pr (by decide)) (hs.fitE m.po (by decide))
    (by rw [imm32_toNat (by have := m.lt; omega_arith)]; exact m.hg) ?_
  rw [view_glue_mem]; exact hr

theorem uh_ok {c : Prog isa} (hc : Callee c (fun stk => useHintContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : UhOk L Wb h r g2 o)
    (hr : Reduced s.mem (lpa L r)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri o 1024, (1, 0, STK)]) s s' →
      NatPolyIs s'.mem (lpa L o) (Vector.zipWith (fun hj rj => (useHint g2 hj rj).toNat)
        ((hintAt s.mem (lpa L h) 1).headD (Vector.replicate n false)) (polyAt s.mem (lpa L r))) → Q s') :
    WP isa (callAt name c (uhArgs h r g2 o)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := uh_cov hs m
  refine callV hver.1 (hs.depth hc.stack hS) m.hg' (uh_preS hs (Nat.le_trans hstk hS) m hr) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri o 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g3, g4, g5, g6⟩ := uh_vg hs m (uhRd L h r) (uhWr L o)
  have := useHint_post hp
  rwa [State.withRegions_mem, g3, g4, g5, g6, view_glue_mem, imm32 (by have := m.lt; omega_arith),
    imm32_toNat (by have := m.lt; omega_arith)] at this

theorem uh_tr {c : Prog isa} (hc : Callee c (fun stk => useHintContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : UhOk L Wb h r g2 o) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L r) ∧
      Reduced y.mem (lpa L r)) :
    RelCT isa P (callAt name c (uhArgs h r g2 o)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg' fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rx, ry⟩ := hP x y hxy
  obtain ⟨gx3, gx4, gx5, gx6⟩ := uh_vg hx m (uhRd L h r) (uhWr L o)
  obtain ⟨gy3, gy4, gy5, gy6⟩ := uh_vg hy m (uhRd L h r) (uhWr L o)
  exact ⟨uhRd L h r, uhWr L o, uh_preS hx (Nat.le_trans hstk hS) m rx, uh_preS hy (Nat.le_trans hstk hS) m ry,
    useHint_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]) (by rw [gx5, gy5])
      (by rw [gx6, gy6]), (uh_cov hx m).1, (uh_cov hx m).2, (uh_cov hy m).1, (uh_cov hy m).2⟩

end

/-! ## `vg_mldsa_unpack_t1` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {v f : Ptr}

abbrev t1Args (v f : Ptr) : List (Reg × Arg) := [(.r3, .ptr v), (.r4, .ptr f)]
abbrev t1Rd (L : Lay) (v : Ptr) : List Region := [L.R (ix v.1) v.2 320]
abbrev t1Wr (L : Lay) (f : Ptr) : List Region := [L.R (ix f.1) f.2 1024]

/-- The facts `vg_mldsa_unpack_t1` needs of its arguments. -/
structure T1Ok (L : Lay) (Wb : List Nat) (v f : Ptr) : Prop where
  pv : PtrIn L v 320
  pf : PtrIn L f 1024
  wf : ix f.1 ∈ Wb
  d1 : sepB L.sizes (tri v 320) (tri f 1024) = true

theorem T1Ok.hg (m : T1Ok L Wb v f) : glueOk (t1Args v f) = true := by
  simp [glueOk, argReg, m.pv.1, m.pf.1]

theorem t1Args_nodup : ((t1Args v f).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide

theorem t1_vg {s : State} (hs : Site L Wb STK s) (m : T1Ok L Wb v f) (rd wr : List Region) :
    (view (glueSt s (t1Args v f)) rd wr).gpr .r3 = lpa L v ∧
    (view (glueSt s (t1Args v f)) rd wr).gpr .r4 = lpa L f :=
  ⟨hs.vG m.hg t1Args_nodup (by simp) m.pv.1 (by decide) _ _, hs.vG m.hg t1Args_nodup (by simp) m.pf.1 (by decide) _ _⟩

theorem t1_cov {s : State} (hs : Site L Wb STK s) (m : T1Ok L Wb v f) :
    Covers (t1Rd L v ++ t1Wr L f) (s.rd ++ s.wr) ∧ Covers (t1Wr L f) s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE m.pv) Covers.nil) (Covers.right (Covers.cons (hs.cwE m.pf m.wf) Covers.nil)),
    Covers.cons (hs.cwE m.pf m.wf) Covers.nil⟩

theorem t1_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : T1Ok L Wb v f) :
    (unpackT1Contract PPC64LE.abi stk).pre (view (glueSt s (t1Args v f)) (t1Rd L v) (t1Wr L f)) := by
  have hsp := view_glue_sp s (t1Args v f) (t1Rd L v) (t1Wr L f)
  obtain ⟨g3, g4⟩ := t1_vg hs m (t1Rd L v) (t1Wr L f)
  exact t1_pre g3 g4 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.dE m.d1 (.inr m.wf))
    (hs.kE m.pv hstk hsp) (hs.kE m.pf hstk hsp) (hs.fitE m.pv (by decide)) (hs.fitE m.pf (by decide))

theorem t1_ok {c : Prog isa} (hc : Callee c (fun stk => unpackT1Contract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : T1Ok L Wb v f) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri f 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (lpa L f) ((simpleBitUnpack (bytesAt s.mem (lpa L v) 320) t1Max).map
        fun c => ofInt (c * 2 ^ d : Nat)) → Q s') :
    WP isa (callAt name c (t1Args v f)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := t1_cov hs m
  refine callV hver.1 (hs.depth hc.stack hS) m.hg (t1_preS hs (Nat.le_trans hstk hS) m) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri f 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g3, g4⟩ := t1_vg hs m (t1Rd L v) (t1Wr L f)
  have := t1_post hp
  rwa [State.withRegions_mem, g3, g4, view_glue_mem] at this

theorem t1_tr {c : Prog isa} (hc : Callee c (fun stk => unpackT1Contract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : T1Ok L Wb v f) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp) :
    RelCT isa P (callAt name c (t1Args v f)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp⟩ := hP x y hxy
  obtain ⟨gx3, gx4⟩ := t1_vg hx m (t1Rd L v) (t1Wr L f)
  obtain ⟨gy3, gy4⟩ := t1_vg hy m (t1Rd L v) (t1Wr L f)
  exact ⟨t1Rd L v, t1Wr L f, t1_preS hx (Nat.le_trans hstk hS) m, t1_preS hy (Nat.le_trans hstk hS) m,
    t1_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]),
    (t1_cov hx m).1, (t1_cov hx m).2, (t1_cov hy m).1, (t1_cov hy m).2⟩

end

end VG.Proof.MlDsa.PPC64LE.KeyGen
