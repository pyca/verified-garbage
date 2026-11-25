module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
public import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Trace
public import VerifiedGarbage.Proof.MlKem.PolyContract
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Forward
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Inverse
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lit
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.MlKem.Mem16Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.MlKem.Arith
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lit

/-! # Calling the NTT of 16-bit coefficients and its inverse -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.Ntt16
open VG.Spec.MlKem (Poly ntt nttInv)
open VG.Proof.MlKem

/-- The memory at `p` holds the words `W`, of `n` bytes. -/
def Holds (m : Mem) (p : Addr) (n : Nat) (W : List (BitVec 64)) : Prop :=
  ∀ i < n / 8, m.readW (p + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0

/-- The table `name` of a transform called on the polynomial at `f`, whose caller has working space
at `w`. -/
structure Ready (name : String) (n : Nat) (W : List (BitVec 64)) (s : State) (f w : Addr) : Prop where
  held : Holds s.mem (s.syms name) n W
  read : Covers [⟨s.syms name, n⟩] (s.rd ++ s.wr)
  output : (Region.mk (s.syms name) n).Disjoint ⟨f, 1024⟩
  scratch : (Region.mk (s.syms name) n).Disjoint ⟨w, 1024⟩

/-- The sizes of the tables. -/
abbrev fwdBytes : Nat := 1152
abbrev invBytes : Nat := 1216

/-- The regions of the tables. -/
abbrev fwdRegion (s : State) : Region := ⟨s.syms Forward.name, fwdBytes⟩
abbrev invRegion (s : State) : Region := ⟨s.syms Inverse.name, invBytes⟩

abbrev FwdReady (s : State) (f w : Addr) : Prop := Ready Forward.name fwdBytes Forward.words s f w
abbrev InvReady (s : State) (f w : Addr) : Prop := Ready Inverse.name invBytes Inverse.words s f w

theorem fwd_length : Forward.words.length = 144 := by lit_decide
theorem inv_length : Inverse.words.length = 152 := by lit_decide

theorem Holds.frame {m m' : Mem} {p : Addr} {n : Nat} {W : List (BitVec 64)} (h : Holds m p n W) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (Region.mk p n).Disjoint r) (hn : n < 2 ^ 32 := by decide) :
    Holds m' p n W := fun i hi => by
  rw [hf.readW (r := ⟨p, n⟩) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hn])) hd (by decide)]
  exact h i hi

theorem Ready.frame {name : String} {n : Nat} {W : List (BitVec 64)} {s t : State} {f w : Addr}
    (h : Ready name n W s f w) (hs : t.syms = s.syms) (hr : t.rd = s.rd) (hw : t.wr = s.wr) {rs : List Region}
    (hf : Frame rs s.mem t.mem) (hd : ∀ r ∈ rs, (Region.mk (s.syms name) n).Disjoint r) (hn : n < 2 ^ 32 := by decide) :
    Ready name n W t f w := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hs]
  · exact h.held.frame hf hd hn
  · rw [hr, hw]; exact h.read
  · exact h.output
  · exact h.scratch

/-! ## The functions -/

/-- The contract of a transform of the polynomial at `x0`, whose table is `name`. -/
def contract (op : Poly → Poly) (name : String) (n : Nat) (W : List (BitVec 64)) : Contract isa where
  pre s := s.rd = [⟨s.syms name, n⟩] ∧ s.wr = [⟨s.gpr .x0, 512⟩] ∧
    (Region.mk (s.syms name) n).Disjoint ⟨s.gpr .x0, 512⟩ ∧ Holds s.mem (s.syms name) n W ∧
    ReducedW 16 s.mem (s.gpr .x0)
  post s s' := PolyIsW 16 s'.mem (s.gpr .x0) (op (polyAtW 16 s.mem (s.gpr .x0)))
  pub _ _ := True

/-- The rows of a table, from its words. -/
theorem rows_of {m : Mem} {p : Addr} {W : List (BitVec 64)} {T : List (List Nat)} (h : Holds m p (16 * T.length) W)
    (hT : ∀ i < T.length, ∀ e < 8, vhalf (ofVDwords (W.getD (2 * i) 0) (W.getD (2 * i + 1) 0)) e = cst (T.getD i []) e) :
    ∀ i < T.length, ∀ e < 8, vhalf (m.read (p + BitVec.ofNat 64 (16 * i)) 16) e = cst (T.getD i []) e := fun i hi e he => by
  have h0 := h (2 * i) (by omega_using [hi])
  have h1 := h (2 * i + 1) (by omega_using [hi])
  rw [show 8 * (2 * i) = 16 * i by omega_using []] at h0
  rw [show 8 * (2 * i + 1) = 16 * i + 8 by omega_using [], BitVec.ofNat_add, ← BitVec.add_assoc] at h1
  rw [read16_dw, h0, show (8#64) = BitVec.ofNat 64 8 from rfl, h1, hT i hi e he]

/-- A transform, from a run of its code on numbered values. -/
theorem correct {op : Poly → Poly} {name : String} {W : List (BitVec 64)} {T : List (List Nat)} {body : List Instr}
    (hT : ∀ i < T.length, ∀ e < 8, vhalf (ofVDwords (W.getD (2 * i) 0) (W.getD (2 * i + 1) 0)) e = cst (T.getD i []) e)
    (hl : T.length ≤ 4096) {D : Dir} {value : (Nat → BitVec 16) → Nat → BitVec 16} (hD : ∀ F, D.Sound (value F)) {k : Nat}
    (hv : ∀ F, ∀ i < 256, value F i = F i)
    (hrun : ((run D T body ⟨List.replicate 32 none, (List.range 32).map fun i => (List.range 8).map fun e => 8 * i + e⟩).map
      fun a => decide (a.mem = (List.range 32).map fun i => (List.range 8).map fun e => k + 8 * i + e)) = some true)
    (hk : ∀ (F : Nat → BitVec 16) (P : Poly), (∀ i < 256, (F i).toNat = (P[i]!).val) →
      ∀ i < 256, (value F (k + i)).toNat = ((op P)[i]!).val) :
    ∀ s, (contract op name (16 * T.length) W).pre s → ∃ tr s', Exec isa (.block (.adrSym .x2 name :: body)) s tr s' ∧
      abiPreserved s s' ∧ (contract op name (16 * T.length) W).post s s' := by
  intro s ⟨hrd, hwr, hd, hh, hr⟩
  obtain ⟨b, hb, hbm⟩ := Option.map_eq_some_iff.1 hrun
  have hbm := of_decide_eq_true hbm
  have cells : ∀ (k : Nat) {i : Nat}, i < 32 → ∀ e < 8,
      (((List.range 32).map fun i => (List.range 8).map fun e => k + 8 * i + e).getD i []).getD e 0 = k + 8 * i + e :=
    fun k i hi e he => by
      rw [List.getD_eq_getElem?_getD (l := List.map _ _), List.getElem?_map, List.getElem?_range hi, Option.map_some,
        Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range he]
      rfl
  let s₀ := s.write .x .x2 (s.syms name)
  have he : Env T (s.gpr .x0) (s.syms name) s₀ := {
    x0 := RegUpd.gpr_write_of_ne _ _ _ (by decide)
    x2 := by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _
    wr := by
      rw [RegUpd.wr_write, hwr]; exact Covers.refl _
    rd := by
      rw [RegUpd.rd_write, RegUpd.wr_write, hrd]; exact Covers.left (Covers.refl _)
    apart := hd
    len := hl
    row := rows_of hh hT }
  let F := fun i => coeffAtW 16 s.mem (s.gpr .x0) i
  have hr0 : Rel (value F) (s.gpr .x0) s₀ ⟨List.replicate 32 none,
      (List.range 32).map fun i => (List.range 8).map fun e => 8 * i + e⟩ s₀ := {
    gpr := rfl, sp := rfl, rd := rfl, wr := rfl
    vcs := fun _ _ => rfl
    frame := Frame.refl _ _
    v := fun r x h => by
      simp only [Regs.get, List.getD_eq_getElem?_getD, List.getElem?_replicate, index_lt r, ↓reduceIte] at h
      cases h
    vlen := rfl
    mlen := rfl
    mem := fun i hi e he' => by
      have := cells 0 hi e he'
      simp only [Nat.zero_add] at this
      rw [this, hv F _ (by omega_using [hi, he'])]
      rfl }
  obtain ⟨tr, s', hx, hr'⟩ := run_sound (hD F) he hb hr0
  have hcons : WP isa (.block (.adrSym .x2 name :: body)) s fun s' => Rel (value F) (s.gpr .x0) s₀ b s' :=
    WP.block_cons_iff.2 ⟨s₀, rfl, ⟨tr, s', hx, hr'⟩⟩
  obtain ⟨tr, s', hx, hr'⟩ := hcons
  have hfin : ∀ i < 256, (coeffAtW 16 s'.mem (s.gpr .x0) i).toNat = ((op (polyAtW 16 s.mem (s.gpr .x0)))[i]!).val :=
    fun i hi => by
      have := hr'.mem (i / 8) (by omega_using [hi]) (i % 8) (by omega_using [])
      rw [hbm, cells k (by omega_using [hi]) _ (by omega_using []), show 8 * (i / 8) + i % 8 = i by omega_using [],
        show k + 8 * (i / 8) + i % 8 = k + i by omega_using []] at this
      rw [this]
      exact hk F _ (fun j hj => polyIsW16_toNat ⟨hr, rfl⟩ hj) i hi
  refine ⟨tr, s', hx, ?_, ?_⟩
  · refine ⟨fun r h => ?_, ?_, fun r h => ?_⟩
    · rw [hr'.gpr]; exact RegUpd.gpr_write_of_ne _ _ _ (fun e => by subst e; exact absurd h (by decide))
    · rw [hr'.sp]; rfl
    · rw [hr'.vcs r h]; rfl
  · refine ⟨fun i hi => by rw [hfin i hi]; exact Fin.isLt _, ext_getElem! fun i hi => ?_⟩
    have e : (polyAtW 16 s'.mem (s.gpr .x0))[i]! = Spec.MlKem.ofNat (coeffAtW 16 s'.mem (s.gpr .x0) i).toNat := by
      rw [getElem!_eq _ hi, polyAtW, Vector.getElem_ofFn]
    rw [e, hfin i hi, ofNat_val]

private theorem fwd_value (F : Nat → BitVec 16) : ∀ i < 256, Forward.value F i = F i := fun i hi => by
  rw [Forward.value, ite_eq_left (by omega_using [hi]), show i / 256 = 0 by omega_using [hi], show i % 256 = i by omega_using [hi]]
  rfl

private theorem inv_value (F : Nat → BitVec 16) : ∀ i < 256, Inverse.value F i = F i := fun i hi => by
  rw [Inverse.value, ite_eq_left (by omega_using [hi]), show i / 512 = 0 by omega_using [hi], show i % 256 = i by omega_using [hi]]
  rfl

private theorem fwd_rows : ∀ i < fwdRows.lit.length, ∀ e < 8,
    vhalf (ofVDwords (Forward.words.getD (2 * i) 0) (Forward.words.getD (2 * i + 1) 0)) e = cst (fwdRows.lit.getD i []) e := by
  lit_decide

private theorem inv_rows : ∀ i < invRows.lit.length, ∀ e < 8,
    vhalf (ofVDwords (Inverse.words.getD (2 * i) 0) (Inverse.words.getD (2 * i + 1) 0)) e = cst (invRows.lit.getD i []) e := by
  lit_decide

theorem fwd_correct : ∀ s, (contract ntt Forward.name fwdBytes Forward.words).pre s →
    ∃ tr s', Exec isa Forward.code s tr s' ∧ abiPreserved s s' ∧
      (contract ntt Forward.name fwdBytes Forward.words).post s s' :=
  correct fwd_rows (by decide) Forward.dir_sound fwd_value Forward.code_run fun _ _ h _ hi => Forward.value_final h hi

theorem inv_correct : ∀ s, (contract nttInv Inverse.name invBytes Inverse.words).pre s →
    ∃ tr s', Exec isa Inverse.code s tr s' ∧ abiPreserved s s' ∧
      (contract nttInv Inverse.name invBytes Inverse.words).post s s' :=
  correct inv_rows (by decide) Inverse.dir_sound inv_value Inverse.code_run fun _ _ h _ hi => Inverse.value_final h hi

/-! ## The calls -/

theorem call_ok {op : Poly → Poly} {fn name : String} {n : Nat} {W : List (BitVec 64)} {c : Prog isa}
    (hv : ∀ s, (contract op name n W).pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ (contract op name n W).post s s')
    (hn : c.noFrames = true) {s : State} {off : Nat} {f w : Addr} {F : Poly} (ho : off < 65536)
    (hf : s.gpr .x28 + BitVec.ofNat 64 off = f) (hp : PolyIsW 16 s.mem f F) (hw : Covers [⟨f, 512⟩] s.wr)
    (hr : Ready name n W s f w) :
    WP isa (.seq (.block (ptrTo .x0 .x28 off)) (.call fn c)) s fun t =>
      Kept [⟨f, 512⟩] s t ∧ PolyIsW 16 t.mem f (op F) := by
  refine WP.seq (WP.mono_syms (wp_ptrTo' (by decide) ho fun s₁ h₁ e₁ => And.intro h₁ e₁) fun s₁ ⟨h₁, e₁⟩ hy => ?_)
  have c0 : s₁.callEntry.gpr .x0 = f := (State.callEntry_gpr s₁ (by decide)).trans (e₁.trans hf)
  have cy : s₁.callEntry.syms = s.syms := hy
  have hsub : Region.Sub ⟨f, 512⟩ ⟨f, 1024⟩ := Region.sub_prefix (by decide)
  refine WP.callV (k := contract op name n W) hv (rd := [⟨s.syms name, n⟩]) (wr := [⟨f, 512⟩]) ?_ ?_ ?_ ?_ hn
  · simp only [contract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_mem, State.callEntry_mem, c0]
    rw [show (s₁.callEntry.withRegions [⟨s.syms name, n⟩] [⟨f, 512⟩]).syms = s.syms from cy, h₁.mem]
    exact ⟨rfl, trivial, hr.output.sub_right hsub, hr.held, hp.1⟩
  · rw [h₁.rd, h₁.wr]; exact Covers.cons hr.read (Covers.right hw)
  · rw [h₁.wr]; exact hw
  · intro t hrd hwr hsp hf' hcs _ hvec hpost
    simp only [contract, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, h₁.mem, hp.2] at hpost
    refine ⟨⟨fun r h1 h2 => ?_, hsp.trans h₁.sp, hrd.trans h₁.rd, hwr.trans h₁.wr, by rw [← h₁.mem]; exact hf',
      fun r h => (hvec r h).trans (h₁.vcs r h)⟩, hpost⟩
    rw [hcs r h1 h2]
    exact h₁.gpr r fun h => by rw [List.mem_singleton.1 h] at h1; exact absurd h1 (by decide)

theorem nttAtWithW_ok {s : State} {off ns : Nat} {f w : Addr} {F : Poly} (ho : off < 65536)
    (hf : s.gpr .x28 + BitVec.ofNat 64 off = f) (hp : PolyIsW 16 s.mem f F) (hw : Covers [⟨f, 512⟩] s.wr)
    (hr : FwdReady s f w) :
    WP isa (Readonly.nttAtWithW off ns) s fun t => Kept [⟨f, 512⟩] s t ∧ PolyIsW 16 t.mem f (ntt F) :=
  call_ok fwd_correct (by lit_decide) ho hf hp hw hr

theorem nttInvAtWithW_ok {s : State} {off ns : Nat} {f w : Addr} {F : Poly} (ho : off < 65536)
    (hf : s.gpr .x28 + BitVec.ofNat 64 off = f) (hp : PolyIsW 16 s.mem f F) (hw : Covers [⟨f, 512⟩] s.wr)
    (hr : InvReady s f w) :
    WP isa (Readonly.nttInvAtWithW off ns) s fun t => Kept [⟨f, 512⟩] s t ∧ PolyIsW 16 t.mem f (nttInv F) :=
  call_ok inv_correct (by lit_decide) ho hf hp hw hr

end VG.Proof.MlKem.AArch64.Ntt16
