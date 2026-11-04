module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.Comb
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.TableCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.Comb
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase

/-! # FFDH key generation from the context on x86-64: the comb in constant time

Every address and count of the comb is a function of its public data, the
comb's `TabP`, the scalar bytes' pointer and their count: the digit is kept
in `r13`, which only the selection's masks read. -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.Cached VG.Impl.Ffdh.X86_64.Cached.Generate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.Rsa.X86_64

/-- The comb's environment, for some scalar bytes of public length. -/
def CE (q : TabP × Addr × Nat) (s : State) : Prop := ∃ xb, xb.length = q.2.2 ∧ CEnv q.1 q.2.1 xb s

/-- The inner workspace's layout. -/
abbrev ceWs (q : TabP × Addr × Nat) : Ws := ⟨off q.1.B q.1.o, slot q.1.w 8, q.1.w⟩

theorem CE.goodW {q : TabP × Addr × Nat} {s : State} (h : CE q s) : GoodW (ceWs q) s := by
  obtain ⟨_, _, he⟩ := h
  exact ⟨q.1.mi, he.good, Nat.le_refl _⟩

theorem CE.rdi {q : TabP × Addr × Nat} {s : State} (h : CE q s) : s.gpr .rdi = off q.1.B q.1.o := by
  obtain ⟨_, _, he⟩ := h
  exact he.good.rdi

theorem CE.keep {q : TabP × Addr × Nat} {s t : State} {rs : List Reg} (h : CE q s) (hm : t.mem = s.mem)
    (k : Keep rs s t) (hd : .rdi ∉ rs) : CE q t := by
  obtain ⟨xb, hl, he⟩ := h
  exact ⟨xb, hl, (he.of_frm (fun x _ => by rw [hm]) k.2.1 k.2.2 (k.gpr hd)).1⟩

theorem pins_ce {α : Type} {Φ : α → State → Prop} (f : α → TabP × Addr × Nat) (h : ∀ a s, Φ a s → CE (f a) s) :
    Pins Φ [.rdi] :=
  pins_rdiB (fun a => off (f a).1.B (f a).1.o) fun a s ha => (h a s ha).rdi

/-- A Montgomery multiplication the backends make in constant time. -/
theorem mmc_ct (Mo : Mont) {o a b : Nat} (hu : MmUse o a b) {α : Type} {Φ : α → State → Prop}
    (f : α → TabP × Addr × Nat) (h : ∀ a s, Φ a s → CE (f a) s) :
    RelCT isa (Two Φ) (Mo.mm o a b) fun _ _ => True :=
  two_map (fun x => ceWs (f x)) (fun x s hx => (h x s hx).goodW) (Mo.ct hu)

/-! ## The digit -/

/-- Row `i`: the comb's environment with `iI = i + 1`. -/
def DgP (p : (TabP × Addr × Nat) × Nat) (s : State) : Prop :=
  CE p.1 s ∧ word s.mem (off p.1.1.B p.1.1.o) (8 * iI) = BitVec.ofNat 64 (p.2 + 1) ∧ p.2 < p.1.1.rows ∧
    5 * p.1.1.rows < 2 ^ 31 ∧ 8 * p.1.2.2 < 2 ^ 32

theorem DgP.keep {p : (TabP × Addr × Nat) × Nat} {s t : State} {rs : List Reg} (h : DgP p s) (hm : t.mem = s.mem)
    (k : Keep rs s t) (hd : .rdi ∉ rs) : DgP p t :=
  ⟨h.1.keep hm k hd, by rw [hm]; exact h.2.1, h.2.2⟩

/-- Before tooth `j`. -/
def TP (j : Nat) (p : (TabP × Addr × Nat) × Nat) (s : State) : Prop :=
  DgP p s ∧ s.gpr .rsi = p.1.2.1 ∧ s.gpr .r9 = BitVec.ofNat 64 p.1.2.2 ∧ ∃ S < 2 ^ j, s.gpr .r13 = BitVec.ofNat 64 S

/-- What tooth `j` pins: `rdi`, the bytes and their count, and the bit's index. -/
def toothVal (j : Nat) (p : (TabP × Addr × Nat) × Nat) (r : Reg) : BitVec 64 :=
  if r = .rax then BitVec.ofNat 64 (p.2 + j * p.1.1.rows) else if r = .rsi then p.1.2.1
  else if r = .r9 then BitVec.ofNat 64 p.1.2.2 else off p.1.1.B p.1.1.o

theorem tooth_ct {j : Nat} (hj : j < 5) {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hA : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rax (.mem (hdr iI)), .alu .sub .rax (.imm 1),
      .mov .rdx (.mem (hdr iRows)), .imul3 .rdx .rdx (BitVec.ofNat 32 j), .alu .add .rax (.reg .rdx)]) hc₁).isSome = true)
    (hB : (taint.check (Taint.ofRegs [.rdi, .rsi, .r9, .rax])
      (.seq bit (.block ((if j = 0 then [] else [.shift .shl .rdx j]) ++ [.alu .or .r13 (.reg .rdx)]))) hc₂).isSome = true) :
    RelCT isa (Two (TP j)) (tooth j) (Two (TP (j + 1))) := by
  unfold tooth
  refine pin_ct [.rdi] [.rdi, .rsi, .r9, .rax] (toothVal j) (pins_ce (fun p => p.1) fun _ _ h => h.1.1) hA
    (fun p s h => ?_) hB (fun p s h => ?_)
  · obtain ⟨⟨hce, hI, _⟩, hsi, h9, _⟩ := h
    obtain ⟨xb, _, he⟩ := hce
    refine WP.mono (toothA_ok he.good (slot8_ge _) hj hI he.rows) fun t ⟨hax, _, k⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (k.gpr (by decide)).trans he.good.rdi
    · exact (k.gpr (by decide)).trans hsi
    · exact (k.gpr (by decide)).trans h9
    · exact hax
  · obtain ⟨hd, hsi, h9, S, hS, h13⟩ := h
    obtain ⟨⟨xb, hl, he⟩, hI, hi, hr, hL⟩ := hd
    have hL' : 8 * xb.length < 2 ^ 32 := by rw [hl]; exact hL
    have hr' : 5 * Spec.Rsa.FixedBaseComb.rows p.1.1.bits < 2 ^ 31 := hr
    refine WP.mono (tooth_ok he.good (slot8_ge _) (xb := xb) hj hI he.rows (by rw [hl]; exact h9) hsi h13 hS
      he.x.rd he.x.val hi hr' hL') fun t ⟨h13', hm, k⟩ => ?_
    have hd' : DgP p s := ⟨⟨xb, hl, he⟩, hI, hi, hr, hL⟩
    refine ⟨hd'.keep hm k (by decide), (k.gpr (by decide)).trans hsi,
      (k.gpr (by decide)).trans h9, _, ?_, h13'⟩
    have hb : Spec.Rsa.os2ip xb / 2 ^ (p.2 + j * p.1.1.rows) % 2 < 2 := Nat.mod_lt _ (by decide)
    rw [Nat.pow_succ]
    rcases (show Spec.Rsa.os2ip xb / 2 ^ (p.2 + j * p.1.1.rows) % 2 = 0 ∨
      Spec.Rsa.os2ip xb / 2 ^ (p.2 + j * p.1.1.rows) % 2 = 1 by omega) with h | h <;> rw [h] <;> omega

theorem digitHead_ok {p : (TabP × Addr × Nat) × Nat} {s : State} (h : DgP p s) :
    WP isa (.block [.mov .rsi (.mem (hdr iXp)), .mov .r9 (.mem (hdr iXl)), .mov32 .r13 (.imm 0)]) s (TP 0 p) := by
  have h' := h
  obtain ⟨⟨xb, hl, he⟩, _⟩ := h'
  have hg := he.good
  have hl' : ∀ k < 32, InRegions (s.rd ++ s.wr) (off (off p.1.1.B p.1.1.o) (8 * k)) 8 :=
    fun k hk => hg.scr.ld (by have := hdr_lt_slot p.1.1.w 8 hk; omega)
  refine WP.mono (WP.keep [.rsi, .r9, .r13] (Q := fun t => t.gpr .rsi = p.1.2.1 ∧
      t.gpr .r9 = BitVec.ofNat 64 p.1.2.2 ∧ t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl' iXp (by decide), hl' iXl (by decide), he.xpw, he.xlw, hl]) rfl)
    fun t ⟨⟨hsi, h9, h13, hm⟩, k⟩ => ⟨h.keep hm k (by decide), hsi, h9, 0, by decide, h13⟩

theorem digit_ct : RelCT isa (Two DgP) digit fun _ _ => True := by
  unfold digit
  refine RelCT.seq (R := Two (TP 0)) (two_piece [.rdi] (pins_ce (fun p => p.1) fun _ _ h => h.1)
    (by taint_decide) fun _ _ h => digitHead_ok h) ?_
  change RelCT isa (Two (TP 0)) (.seq (tooth 0) (.seq (tooth 1) (.seq (tooth 2) (.seq (tooth 3) (tooth 4))))) _
  exact RelCT.seq (tooth_ct (j := 0) (by decide) (by taint_decide) (by taint_decide))
    (RelCT.seq (tooth_ct (j := 1) (by decide) (by taint_decide) (by taint_decide))
      (RelCT.seq (tooth_ct (j := 2) (by decide) (by taint_decide) (by taint_decide))
        (RelCT.seq (tooth_ct (j := 3) (by decide) (by taint_decide) (by taint_decide))
          ((tooth_ct (j := 4) (by decide) (by taint_decide) (by taint_decide)).mono (fun _ _ h => h)
            fun _ _ _ => trivial))))

/-! ## The selection -/

/-- Entry `e` of the scan. -/
def SA (T : TabP) (e : Nat) (t : State) : Prop :=
  ∃ E d s, SelB T.B T.Z T.o T.w T.mi T.cp E d s ∧ SelO T.B T.o T.w E d s e t

def SM (p : TabP × Nat) (t : State) : Prop := p.2 < 32 ∧ ∃ E d s, SelB p.1.B p.1.Z p.1.o p.1.w p.1.mi p.1.cp E d s ∧
  SelO p.1.B p.1.o p.1.w E d s p.2 t ∧ t.gpr .rax = BitVec.ofNat 64 (p.2 + 2) ∧ t.gpr .rdx = eqMask p.2 d

def SR (p : TabP × Nat) (t : State) : Prop := p.2 < 32 ∧ ∃ E d s, SelB p.1.B p.1.Z p.1.o p.1.w p.1.mi p.1.cp E d s ∧
  SelO p.1.B p.1.o p.1.w E d s p.2 t ∧ t.gpr .rdx = eqMask p.2 d ∧
    t.gpr .rsi = off p.1.cp (24 + 8 * p.1.w * (p.2 + 2)) ∧ t.gpr .rbx = off (off p.1.B p.1.o) (slot p.1.w aXm) ∧
    t.gpr .r12 = BitVec.ofNat 64 p.1.w

def SF (p : TabP × Nat) (t : State) : Prop := p.2 < 32 ∧ ∃ E d s, SelB p.1.B p.1.Z p.1.o p.1.w p.1.mi p.1.cp E d s ∧
  SelF p.1.B p.1.o p.1.w E d s p.2 t

theorem SelO.rdi {B : Addr} {Z o w : Nat} {mi : BitVec 64} {cp : Addr} {E : Nat → Nat → BitVec 64} {d e : Nat}
    {s t : State} (hb : SelB B Z o w mi cp E d s) (hI : SelO B o w E d s e t) : t.gpr .rdi = off B o :=
  (hI.facts hb).1.rdi

theorem SelF.rdi {B : Addr} {Z o w : Nat} {mi : BitVec 64} {cp : Addr} {E : Nat → Nat → BitVec 64} {d e : Nat}
    {s t : State} (hb : SelB B Z o w mi cp E d s) (hF : SelF B o w E d s e t) : t.gpr .rdi = off B o :=
  (hF.2.2.2.gpr (by decide)).trans hb.hc.rdi

theorem selectStep_ct :
    RelCT isa (Two fun (p : TabP × Nat) t => p.2 < 32 ∧ SA p.1 p.2 t) selectStep fun _ _ => True := by
  rw [selectStep_eq]
  refine RelCT.seq (R := Two SM) (two_piece [.rdi] (pins_rdiB (fun p => off p.1.B p.1.o) fun _ _ h => by
      obtain ⟨_, E, d, s, hb, hI⟩ := h; exact hI.rdi hb) (by taint_decide) fun p t h => ?_) ?_
  · obtain ⟨he, E, d, s, hb, hI⟩ := h
    exact WP.mono (selMask_ok hb he hI) fun u ⟨hu, hax, hdx⟩ => ⟨he, E, d, s, hb, hu, hax, hdx⟩
  refine RelCT.seq (R := Two SR) (two_piece [.rdi, .rax] (pins_of (fun p r => if r = .rdi then off p.1.B p.1.o
      else BitVec.ofNat 64 (p.2 + 2)) fun p t h r hr => by
        obtain ⟨_, E, d, s, hb, hI, hax, _⟩ := h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hI.rdi hb
        · exact hax) (by taint_decide) fun p t h => ?_) ?_
  · obtain ⟨he, E, d, s, hb, hI, hax, hdx⟩ := h
    exact WP.mono (selRow_ok hb hI hax hdx) fun u ⟨hu, hdx', hsi, hbx, h12⟩ => ⟨he, E, d, s, hb, hu, hdx', hsi, hbx, h12⟩
  refine RelCT.seq (R := Two SF) (two_piece [.rdi, .rsi, .rbx, .r12] (pins_of (fun p r => if r = .rdi then off p.1.B p.1.o
      else if r = .rsi then off p.1.cp (24 + 8 * p.1.w * (p.2 + 2)) else if r = .rbx then off (off p.1.B p.1.o) (slot p.1.w aXm)
      else BitVec.ofNat 64 p.1.w) fun p t h r hr => by
        obtain ⟨_, E, d, s, hb, hI, _, hsi, hbx, h12⟩ := h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hI.rdi hb
        · exact hsi
        · exact hbx
        · exact h12) (by taint_decide) fun p t h => ?_) ?_
  · obtain ⟨he, E, d, s, hb, hI, hdx, hsi, hbx, h12⟩ := h
    exact WP.mono (selWords_ok hb he hI hdx hsi hbx h12) fun u hu => ⟨he, E, d, s, hb, hu⟩
  exact two_taint [.rdi] (pins_rdiB (fun p => off p.1.B p.1.o) fun _ _ h => by
    obtain ⟨_, E, d, s, hb, hF⟩ := h; exact hF.rdi hb) (by taint_decide)

/-- The scan's start: the entries' words, the digit and `aXm`'s words zero. -/
def SelStart (T : TabP) (s : State) : Prop := ∃ E d, SelB T.B T.Z T.o T.w T.mi T.cp E d s ∧
  ∀ i < T.w, word s.mem (off T.B T.o) (slot T.w aXm + 8 * i) = 0#64

theorem select_ct : RelCT isa (Two SelStart) select (Two fun (T : TabP) t => ∃ E d s,
    SelB T.B T.Z T.o T.w T.mi T.cp E d s ∧ SelO T.B T.o T.w E d s 32 t) := by
  unfold select
  simp only [seqs]
  refine RelCT.seq (R := Two fun (T : TabP) t => 0 < 32 ∧ SA T 0 t) (two_piece [.rdi]
    (pins_rdiB (fun T => off T.B T.o) fun _ _ h => by obtain ⟨E, d, hb, _⟩ := h; exact hb.hc.rdi)
    (by taint_decide) fun T s h => ?_) ?_
  · obtain ⟨E, d, hb, hz⟩ := h
    have hc := hb.hc
    have hn := hc.scr.nowrap
    have hi := hc.hi
    have hlo := hc.lo
    have hsx := slot_le (w := T.w) (show aXm < 8 by decide)
    have hlE := hdr_lt_slot T.w 8 (show iE < 32 by decide)
    have hsc := hc.good.scr
    refine WP.mono (WP.keep [.rax] (Q := fun u =>
        u.mem = s.mem.writeW (off (off T.B T.o) (8 * iE)) (BitVec.ofNat 64 0)) (by
      xrun [State.ea, hdr, hc.good.rdi, hdrOff, hsc.st (d := 8 * iE) (by omega)]; rfl) rfl)
      fun t₀ ⟨hm₀, k₀⟩ => ⟨by decide, E, d, s, hb, ?_⟩
    have ho₀ := writeW_outside s.mem (off T.B T.o) (d := 8 * iE) (BitVec.ofNat 64 0) (by omega)
    rw [← hm₀] at ho₀
    exact ⟨Frm.of_outside ho₀ (by simp [selR]), by rw [hm₀]; exact word_writeW_self _ _ _ _,
      fun i hi' => by
        rw [ho₀.word (Or.inr (by have := hdr_lt_slot T.w aXm (show iE < 32 by decide); omega)) (by omega), hz i hi']
        rfl, k₀.mono (by decide)⟩
  refine two_loop (Φ := SA) (N := fun _ => 32) selectStep_ct ?_
  intro T e t he ⟨E, d, s, hb, hI⟩
  refine WP.mono (selectStep_ok hb he hI) fun u ⟨hz, hu⟩ =>
    ⟨eval_ne_step he hz, fun _ => ⟨E, d, s, hb, hu⟩, fun h => ⟨E, d, s, hb, h ▸ hu⟩⟩

end VG.Proof.Ffdh.X86_64.Cached
