import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Comp
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTLemmas

/-!
# RSA with AVX512_IFMA on x86-64, any size: constant time, a prime's region

`region l p` is `k1` (a copy and `doubles`,
whose `-p⁻¹` is secret: `doublesW_ct`), then blocks that read pointers from
the headers and `n`'s slots (`RT`), the same in two runs with the same
public data, each checked by the taint analysis after its loads
(`ct_split`). The checks of the code that depends on the layout are
`RegT l`, which `regT` evaluates for each layout. `region0_ct`,
`region1_ct`: the regions are constant time for `region_ok`'s hypotheses
(`RegPre`).
-/

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64 (ct_split pins_eqs doublesW_ct DblPreW ct_cons)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-! ## The taint checks of the code that depends on the layout -/

/-- `c` passes the taint analysis from the public registers `rs`. -/
def TOk (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc : VG.Taint.Hint VG.X86_64.Taint.T, (taint.check (Taint.ofRegs rs) c hc).isSome = true

/-- `arr52`'s code after its loads. -/
def arrTail (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p c : Nat) : List Instr :=
  ([.alu .add .r11 (.imm (BitVec.ofNat 32 (l.D * p + c))), .movImm64 .r12 mask52] : List Instr) ++ to52 l

/-- `k0St`'s code after its load. -/
def k0Tail (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : Nat) : List Instr :=
  ([.alu .add .r11 (.imm (BitVec.ofNat 32 (l.D * p))), .mov .rax (.mem (hdr sMinv)), .alu .and .rax (.reg .r12)] :
    List Instr) ++ (List.range 4).map (fun i => .store (at_ .r11 (l.oK0 + 8 * i)) .rax)

/-- The region's checks that depend on the layout. -/
structure RegT (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Prop where
  a0M : TOk [.rsi, .r11] (.block (arrTail l 0 oM))
  a0K1 : TOk [.rsi, .r11] (.block (arrTail l 0 l.oK1))
  a0X : TOk [.rsi, .r11] (.block (arrTail l 0 l.oX))
  a0Y : TOk [.rsi, .r11] (.block (arrTail l 0 l.oY))
  a0F : TOk [.rsi, .r11] (.block (arrTail l 0 l.oFin))
  a1M : TOk [.rsi, .r11] (.block (arrTail l 1 oM))
  a1K1 : TOk [.rsi, .r11] (.block (arrTail l 1 l.oK1))
  a1X : TOk [.rsi, .r11] (.block (arrTail l 1 l.oX))
  a1Y : TOk [.rsi, .r11] (.block (arrTail l 1 l.oY))
  k00 : TOk [.rdi, .r11] (.block (k0Tail l 0))
  k01 : TOk [.rdi, .r11] (.block (k0Tail l 1))
  eZ : TOk [.r11] (.block (eZero l))
  fin : TOk [.r11] (.block (finOne l))
  eEnd : TOk [.rcx, .r11] (.block [.alu .add .r11 (.imm (BitVec.ofNat 32 (l.oE + l.E))), .alu .sub .r11 (.reg .rcx)])
  cnt : TOk [.rdi] (.block [.mov32 .rcx (.imm (BitVec.ofNat 32 l.dbls))])

theorem regT (hl : LayOk l) : RegT l := by
  rcases hl with rfl | rfl | rfl <;>
    exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

/-! ## The region's public data and what its blocks read -/

/-- The public data of a region: `n`'s workspace `B` (of `Z` bytes), the
prime's at `off B o`, the area at `off B a`, `n`'s slots of the exponent's
pointer `ep` and length `L`. -/
structure RegPub where
  B : Addr
  Z : Nat
  o : Nat
  a : Nat
  ep : Addr
  L : Nat

/-- The prime's workspace. -/
abbrev RegPub.pw (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (q : RegPub) : Ws := ⟨off q.B q.o, slot l.W 8, l.W⟩

/-- The layout of region `p`. -/
def RegPub.Ok (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (q : RegPub) (p sp sl : Nat) : Prop :=
  q.o + slot l.W 8 + tabBytes l.W ≤ q.a ∧ q.a + 2 * l.D + 8 ≤ q.Z ∧ p < 2 ∧ sp < 32 ∧ sl < 32 ∧ 1 ≤ q.L ∧
    q.L ≤ l.E

/-- What the region's blocks read (`TCtx`). -/
def RT (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p sp sl : Nat) (q : RegPub) (s : State) : Prop :=
  q.Ok l p sp sl ∧ ∃ (mx : BitVec 64) (eb : List Byte), TCtx l s q.B q.Z q.o q.a mx sp sl q.ep eb ∧ eb.length = q.L

theorem RT.of_frm {p sp sl : Nat} {q : RegPub} {s t : State} (h : RT l p sp sl q s) {rs : List (Nat × Nat)}
    (hf : Frm q.B rs s.mem t.mem) (hr : ∀ r ∈ rs, q.a ≤ r.1 ∧ r.1 + r.2 ≤ q.Z)
    (k : Keep [.rax, .rcx, .rbp, .rsi, .r11, .r12] s t) : RT l p sp sl q t := by
  obtain ⟨ok, mx, eb, c, hl⟩ := h
  have hok := ok
  obtain ⟨hoa, haZ, _, hsp, hsl, _⟩ := ok
  exact ⟨hok, mx, eb, c.of_frm hf hr hoa (by omega) hsp hsl k, hl⟩

theorem RT.rdi {p sp sl : Nat} {q : RegPub} {s : State} (h : RT l p sp sl q s) : s.gpr .rdi = off q.B q.o :=
  let ⟨_, _, _, c, _⟩ := h; c.rdi

theorem pins_rt {p sp sl : Nat} {Φ : RegPub → State → Prop} (h : ∀ q s, Φ q s → RT l p sp sl q s) :
    Pins Φ [.rdi] :=
  pins_eqs (fun q _ => off q.B q.o) fun q s hs r hr => by
    rw [List.mem_singleton.mp hr]; exact (RT.rdi (h q s hs))

/-- The header's slots of the prime's workspace can be read. -/
theorem RT.hd {p sp sl : Nat} {q : RegPub} {s : State} (h : RT l p sp sl q s) :
    ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off q.B q.o) (8 * i)) 8 := fun i hi => by
  obtain ⟨⟨hoa, haZ, -⟩, mx, eb, c, -⟩ := h
  have := hdr_lt_slot l.W 8 hi
  rw [off_off]; exact c.scr.ld (by omega)

/-! ## The blocks -/

theorem arr52_eq (p j c : Nat) : arr52 l p j c =
    ([.mov .rsi (.mem (hdr (sArr j))), .mov .r11 (.mem (hdr sIfma))] : List Instr) ++ arrTail l p c := by
  simp only [arr52, arrTail, List.cons_append, List.nil_append]

/-- `arr52`'s loads: the array's and the area's addresses. -/
theorem arrLd_ok {p j sp sl : Nat} (hj : j < 8) {q : RegPub} {s : State} (h : RT l p sp sl q s) :
    WP isa (.block [.mov .rsi (.mem (hdr (sArr j))), .mov .r11 (.mem (hdr sIfma))]) s fun t =>
      t.gpr .rsi = off (off q.B q.o) (slot l.W j) ∧ t.gpr .r11 = off q.B q.a := by
  have hH := h.hd
  obtain ⟨-, mx, eb, c, -⟩ := h
  refine WP.mono (WP.keep [.rsi, .r11] (Q := fun t => t.gpr .rsi = off (off q.B q.o) (slot l.W j) ∧
    t.gpr .r11 = off q.B q.a) (by
      xrun [State.ea, hdr, c.rdi, hdrOff, hH _ (show sArr j < 32 by unfold sArr; omega), hH sIfma (by decide)]
      exact ⟨c.hdr.harr j hj, c.ia⟩) rfl) fun t h => h.1

theorem arr52_rt (hl : LayOk l) {p j c sp sl : Nat} (hc : c + l.NB ≤ l.D) (hj : j < 8) {q : RegPub} {s : State}
    (h : RT l p sp sl q s) : WP isa (.block (arr52 l p j c)) s fun t => RT l p sp sl q t ∧ t.gpr .r12 = mask52 := by
  have hRT := h
  obtain ⟨⟨hoa, haZ, hp, -⟩, mx, eb, c', -⟩ := h
  have hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega
  exact WP.mono (arr52r_ok hl c'.scr c'.rdi c'.hdr c'.ia hoa haZ hp hc hj) fun t ⟨_, f, k, h12, _⟩ =>
    ⟨hRT.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) k, h12⟩

/-- `arr52` is constant time, given that the taint analysis checks the rest after its loads. -/
theorem arr52_ct {p j c sp sl : Nat} (hj : j < 8) {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT₁ : (taint.check (Taint.ofRegs [.rdi]) (.block ([.mov .rsi (.mem (hdr (sArr j))),
      .mov .r11 (.mem (hdr sIfma))] : List Instr)) hc₁).isSome = true)
    (hT : TOk [.rsi, .r11] (.block (arrTail l p c))) :
    RelCT isa (Two (RT l p sp sl)) (.block (arr52 l p j c)) fun _ _ => True := by
  rw [arr52_eq]
  obtain ⟨_, hT⟩ := hT
  exact ct_split _ _ [.rdi] [.rsi, .r11] (pins_rt fun _ _ h => h) hT₁
    (fun _ _ h => arrLd_ok hj h)
    (pins_eqs (fun q r => if r = .rsi then off (off q.B q.o) (slot l.W j) else off q.B q.a) fun q s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2) hT

theorem k0St_eq (p : Nat) : k0St l p = ([.mov .r11 (.mem (hdr sIfma))] : List Instr) ++ k0Tail l p := by
  simp only [k0St, k0Tail, List.cons_append, List.nil_append]

theorem k0St_rt (hl : LayOk l) {p sp sl : Nat} {q : RegPub} {s : State} (h : RT l p sp sl q s ∧ s.gpr .r12 = mask52) :
    WP isa (.block (k0St l p)) s fun t => RT l p sp sl q t ∧ t.gpr .r11 = off (off q.B q.a) (l.D * p) := by
  have hRT := h.1
  obtain ⟨⟨⟨hoa, haZ, hp, -⟩, mx, eb, c, -⟩, h12⟩ := h
  have hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega
  obtain ⟨o1, -⟩ := lay_offs l
  obtain ⟨hDb1, -⟩ := hl.D_bounds
  have := hl.D_ge
  exact WP.mono (k0r_ok hl c.scr c.rdi c.hdr c.ia hoa haZ hp h12) fun t ⟨_, f, r11, k⟩ =>
    ⟨hRT.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) (k.mono (by decide)), r11⟩

theorem k0St_ct (p : Nat) {sp sl : Nat} (hT : TOk [.rdi, .r11] (.block (k0Tail l p))) :
    RelCT isa (Two fun q s => RT l p sp sl q s ∧ s.gpr .r12 = mask52) (.block (k0St l p)) fun _ _ => True := by
  rw [k0St_eq]
  obtain ⟨_, hT⟩ := hT
  refine ct_split (Ψ := fun q t => t.gpr .rdi = off q.B q.o ∧ t.gpr .r11 = off q.B q.a) _ _ [.rdi] [.rdi, .r11]
    (pins_rt fun _ _ h => h.1) (by taint_decide) (fun q s h => ?_)
    (pins_eqs (fun q r => if r = .rdi then off q.B q.o else off q.B q.a) fun q s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2) hT
  have hH := h.1.hd
  obtain ⟨⟨-, mx, eb, c, -⟩, -⟩ := h
  exact WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = off q.B q.a) (by
    xrun [State.ea, hdr, c.rdi, hdrOff, hH sIfma (by decide)]; exact c.ia) rfl) fun t ⟨h11, k⟩ =>
      ⟨(k.gpr (by decide)).trans c.rdi, h11⟩

theorem eZero_rt (hl : LayOk l) {p sp sl : Nat} {q : RegPub} {s : State}
    (h : RT l p sp sl q s ∧ s.gpr .r11 = off (off q.B q.a) (l.D * p)) :
    WP isa (.block (eZero l)) s fun t =>
      RT l p sp sl q t ∧ t.gpr .r11 = off (off q.B q.a) (l.D * p) ∧ t.gpr .rax = 0 := by
  have hRT := h.1
  obtain ⟨⟨⟨hoa, haZ, hp, -⟩, mx, eb, c, -⟩, h11⟩ := h
  have hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega
  obtain ⟨-, -, -, -, -, o6, o7, o8, o9, o10⟩ := lay_offs l
  exact WP.mono (eZr_ok hl c.scr haZ hp h11) fun t ⟨_, f, ra, k⟩ =>
    ⟨hRT.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) (k.mono (by decide)),
      (k.gpr (by decide)).trans h11, ra⟩

theorem eZero_ct (p : Nat) {sp sl : Nat} (hT : TOk [.r11] (.block (eZero l))) :
    RelCT isa (Two fun q s => RT l p sp sl q s ∧ s.gpr .r11 = off (off q.B q.a) (l.D * p)) (.block (eZero l))
      fun _ _ => True :=
  let ⟨_, hT⟩ := hT
  two_taint [.r11] (pins_eqs (fun q _ => off (off q.B q.a) (l.D * p))
    fun q s (h : RT l p sp sl q s ∧ s.gpr .r11 = off (off q.B q.a) (l.D * p)) r hr => by
      rw [List.mem_singleton.mp hr]; exact h.2) hT

theorem finOne_rt (hl : LayOk l) {sp sl : Nat} {q : RegPub} {s : State}
    (h : RT l 1 sp sl q s ∧ s.gpr .r11 = off (off q.B q.a) (l.D * 1) ∧ s.gpr .rax = 0) :
    WP isa (.block (finOne l)) s fun t => RT l 1 sp sl q t ∧ t.gpr .r11 = off (off q.B q.a) (l.D * 1) := by
  have hRT := h.1
  obtain ⟨⟨⟨hoa, haZ, hp, -⟩, mx, eb, c, -⟩, h11, ha⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, o9, o10⟩ := lay_offs l
  exact WP.mono (finr_ok hl c.scr haZ h11 ha) fun t ⟨_, f, k⟩ =>
    ⟨hRT.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) (k.mono (by decide)),
      (k.gpr (by decide)).trans h11⟩

theorem finOne_ct {sp sl : Nat} (hT : TOk [.r11] (.block (finOne l))) :
    RelCT isa (Two fun q s => RT l 1 sp sl q s ∧ s.gpr .r11 = off (off q.B q.a) (l.D * 1) ∧ s.gpr .rax = 0)
      (.block (finOne l)) fun _ _ => True :=
  let ⟨_, hT⟩ := hT
  two_taint [.r11] (pins_eqs (fun q _ => off (off q.B q.a) (l.D * 1))
    fun q s (h : RT l 1 sp sl q s ∧ s.gpr .r11 = off (off q.B q.a) (l.D * 1) ∧ s.gpr .rax = 0) r hr => by
      rw [List.mem_singleton.mp hr]; exact h.2.1) hT

/-! ## The exponent's copy -/

/-- After `eCopy`'s first block: the pointer, the length and the destination. -/
def ECp (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : Nat) (q : RegPub) (t : State) : Prop :=
  t.gpr .rsi = q.ep ∧ t.gpr .rcx = BitVec.ofNat 64 q.L ∧
    t.gpr .r11 = off (off (off q.B q.a) (l.D * p)) (l.oE + l.E - q.L)

theorem eBlk_ok (hl : LayOk l) {p sp sl : Nat} {q : RegPub} {s : State}
    (h : RT l p sp sl q s ∧ s.gpr .r11 = off (off q.B q.a) (l.D * p)) :
    WP isa (.block [.mov .rax (.mem (hdr sLink)), .mov .rsi (.mem (ws .rax sp)), .mov .rcx (.mem (ws .rax sl)),
      .alu .add .r11 (.imm (BitVec.ofNat 32 (l.oE + l.E))), .alu .sub .r11 (.reg .rcx)]) s (ECp l p q) := by
  have hH := h.1.hd
  obtain ⟨⟨⟨hoa, haZ, hp, hsp, hsl, hL1, hL2⟩, mx, eb, c, hl'⟩, h11⟩ := h
  have hn := c.scr.nowrap
  have h8 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  obtain ⟨-, -, -, -, -, o6, -, -, -, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  have hlv₁ : s.mem.readW (off (off q.B q.o) (8 * sLink)) 64 = q.B := c.lk
  have hp' : InRegions (s.rd ++ s.wr) (off q.B (8 * sp)) 8 := c.scr.ld (by omega)
  have hl'' : InRegions (s.rd ++ s.wr) (off q.B (8 * sl)) 8 := c.scr.ld (by omega)
  have hlv' : word s.mem q.B (8 * sl) = BitVec.ofNat 64 q.L := by rw [← hl']; exact c.lv
  refine WP.mono (WP.keep [.rax, .rcx, .rsi, .r11] (Q := fun t => t.gpr .rsi = q.ep ∧
    t.gpr .rcx = BitVec.ofNat 64 q.L ∧ t.gpr .r11 = off (off (off q.B q.a) (l.D * p)) (l.oE + l.E - q.L)) (by
    xrun [State.ea, hdr, ws, c.rdi, hdrOff, hH sLink (by decide), hlv₁, hp', hl'',
      AmmSym.se_ofNat (show l.oE + l.E < 2 ^ 31 by omega)]
    and_intros
    · exact c.pv
    · exact hlv'
    rw [show s.mem.readW (off q.B (8 * sl)) 64 = BitVec.ofNat 64 q.L from hlv', h11,
      VG.Offset.add_ofNat_sub _ (by omega)]) rfl) fun t h => h.1

/-- `eCopy` is constant time, given that the taint analysis checks its loads
from `n`'s workspace. -/
theorem eCopy_ct (hl : LayOk l) {p sp sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rax]) (.block [.mov .rsi (.mem (ws .rax sp)),
      .mov .rcx (.mem (ws .rax sl))]) hc).isSome = true)
    (hE : TOk [.rcx, .r11] (.block [.alu .add .r11 (.imm (BitVec.ofNat 32 (l.oE + l.E))), .alu .sub .r11 (.reg .rcx)])) :
    RelCT isa (Two fun q s => RT l p sp sl q s ∧ s.gpr .r11 = off (off q.B q.a) (l.D * p))
      (seqs (eCopy l sp sl)) fun _ _ => True := by
  obtain ⟨_, hE⟩ := hE
  show RelCT isa _ (.seq (.block (([.mov .rax (.mem (hdr sLink))] : List Instr) ++
    (([.mov .rsi (.mem (ws .rax sp)), .mov .rcx (.mem (ws .rax sl))] : List Instr) ++
      ([.alu .add .r11 (.imm (BitVec.ofNat 32 (l.oE + l.E))), .alu .sub .r11 (.reg .rcx)] : List Instr)))) _) _
  refine RelCT.seq (two_post (Ψ := ECp l p) ?_ fun q s h => eBlk_ok hl h)
    (two_taint [.rsi, .rcx, .r11] (pins_eqs (fun q r => if r = .rsi then q.ep else if r = .rcx then
      BitVec.ofNat 64 q.L else off (off (off q.B q.a) (l.D * p)) (l.oE + l.E - q.L)) fun q s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2) (by taint_decide))
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun q t => (RT l p sp sl q t ∧
      t.gpr .r11 = off (off q.B q.a) (l.D * p)) ∧ t.gpr .rax = q.B) [.rdi]
    (pins_rt fun _ _ h => h.1) (by taint_decide) ?_) (RelCT.block_append (RelCT.seq (two_piece
      (Ψ := fun q t => t.gpr .rcx = BitVec.ofNat 64 q.L ∧ t.gpr .r11 = off (off q.B q.a) (l.D * p)) [.rax]
      (pins_eqs (fun q _ => q.B) fun q s h r hr => by rw [List.mem_singleton.mp hr]; exact h.2) hT ?_)
    (two_taint [.rcx, .r11] (pins_eqs (fun q r => if r = .rcx then BitVec.ofNat 64 q.L else
      off (off q.B q.a) (l.D * p)) fun q s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) hE))))
  · rintro q s ⟨hRT, h11⟩
    have hH := hRT.hd
    have hRT' := hRT
    obtain ⟨-, mx, eb, c, -⟩ := hRT'
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = q.B ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, c.rdi, hdrOff, hH sLink (by decide)]; exact c.lk) rfl) fun t ⟨⟨ha, hm⟩, k⟩ =>
        ⟨⟨hRT.of_frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (k.mono (by decide)),
          (k.gpr (by decide)).trans h11⟩, ha⟩
  · rintro q s ⟨⟨hRT, h11⟩, ha⟩
    obtain ⟨⟨hoa, haZ, hp, hsp, hsl, -⟩, mx, eb, c, hl'⟩ := hRT
    have hn := c.scr.nowrap
    have h8 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
    have hp' : InRegions (s.rd ++ s.wr) (off q.B (8 * sp)) 8 := c.scr.ld (by omega)
    have hl'' : InRegions (s.rd ++ s.wr) (off q.B (8 * sl)) 8 := c.scr.ld (by omega)
    refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 q.L) (by
      xrun [State.ea, ws, ha, hdrOff, hp', hl'']; rw [← hl']; exact c.lv) rfl) fun t ⟨hcx, k⟩ =>
        ⟨hcx, (k.gpr (by decide)).trans h11⟩

/-! ## `k1`, and the region -/

/-- `region_ok`'s hypotheses. -/
def RegPre (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p sp sl : Nat) (q : RegPub) (s : State) : Prop :=
  q.Ok l p sp sl ∧ ∃ (w : Nat) (mx : BitVec 64) (X : Nat) (eb : List Byte), SubCtx s q.B q.Z q.o w l.W mx ∧
    word s.mem (off q.B q.o) (8 * sIfma) = off q.B q.a ∧ wv s.mem (off q.B q.o) (slot l.W Public.aN) l.W = X ∧
    wv s.mem (off q.B q.o) (slot l.W Public.aY) l.W < X ∧ word s.mem q.B (8 * sp) = q.ep ∧
    word s.mem q.B (8 * sl) = BitVec.ofNat 64 eb.length ∧ Src s q.B q.Z q.ep eb ∧ eb.length = q.L

/-- Before `doubles`. -/
def K2 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p sp sl : Nat) (q : RegPub) (s : State) : Prop :=
  DblPreW Public.aN aT (q.pw l, l.dbls) s ∧
    WP isa (doubles Public.aN Public.aAcc Public.aTmp aT sCtr) s (RT l p sp sl q)

/-- Before `doubles`' count. -/
def K1 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p sp sl : Nat) (q : RegPub) (s : State) : Prop :=
  s.gpr .rdi = off q.B q.o ∧ WP isa (.block [.mov32 .rcx (.imm (BitVec.ofNat 32 l.dbls))]) s (K2 l p sp sl q)

/-- Before `k1`. -/
def K0 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p sp sl : Nat) (q : RegPub) (s : State) : Prop :=
  GoodW (q.pw l) s ∧ WP isa (seqs (copyArr aT Public.aY)) s (K1 l p sp sl q)

/-- `region_ok`'s hypotheses give `K0`, as `k1_ok` runs `k1`. -/
theorem k1_chain (hl : LayOk l) {p sp sl : Nat} {q : RegPub} {s : State} (h : RegPre l p sp sl q s) :
    K0 l p sp sl q s := by
  obtain ⟨ok, w, mx, X, eb, hc, hia, hN, hY, hpv, hlv, he, hl'⟩ := h
  have hok := ok
  obtain ⟨hoa, haZ, hp, hsp, hsl, hL1, hL2⟩ := ok
  have hn := hc.scr.nowrap
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  have h16 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  have hg := hc.good
  have lT := slot_le (w := l.W) (show aT < 8 by decide)
  have lN := slot_le (w := l.W) (show Public.aN < 8 by decide)
  have sTN := slot_sep (w := l.W) (show aT ≠ Public.aN by decide)
  have hdb : 1 ≤ l.dbls ∧ l.dbls < 2 ^ 31 := by rcases hl with rfl | rfl | rfl <;> decide
  have hk1 : ∀ r ∈ k1Ranges l.W, r.1 + r.2 ≤ slot l.W 8 := by
    have := slot_le (w := l.W) (show Public.aAcc < 8 by decide)
    have := slot_le (w := l.W) (show Public.aTmp < 8 by decide)
    have := hdr_lt_slot l.W 8 (show sCtr < 32 by decide)
    simp only [k1Ranges, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> omega
  refine ⟨⟨mx, hg, Nat.le_refl _⟩, WP.mono (copyArr_ok hg (Nat.le_refl _) (by omega) (by omega) (o := aT)
    (a := Public.aY) (by decide) (by decide) (by decide)) fun s₁ ⟨hv₁, ho₁, k₁⟩ => ?_⟩
  have hg₁ := hg.of_outsideArr ho₁ k₁
  have hN₁ : wv s₁.mem (off q.B q.o) (slot l.W Public.aN) l.W = X := by
    rw [ho₁.wv (by omega) (by omega)]; exact hN
  refine ⟨hg₁.rdi, WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 l.dbls ∧ t.mem = s₁.mem) (by
    xrun; and_intros
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]) rfl)
    fun s₂ ⟨⟨cx₂, me₂⟩, k₂⟩ => ?_⟩
  have hg₂ : VG.Proof.Bignum.X86_64.Good s₂ (off q.B q.o) (slot l.W 8) l.W mx :=
    ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, by rw [me₂]; exact hg₁.hdr⟩
  refine ⟨⟨⟨mx, hg₂, Nat.le_refl _⟩, show 2 ≤ l.W by omega, show l.W < 2 ^ 31 by omega, hdb.1, hdb.2, cx₂,
    by rw [me₂, hv₁, hN₁]; exact hY⟩, ?_⟩
  refine WP.mono (doubles_ok hg₂.scr hg₂.rdi hg₂.hdr (Nat.le_refl _) (by omega) (by omega) (mo := Public.aN)
    (acc := Public.aAcc) (tmp := Public.aTmp) (o := aT) (sl := sCtr) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (c := l.dbls) hdb.1 hdb.2 cx₂ (by rw [me₂, hv₁, hN₁]; exact hY)) fun t ⟨_, hf, hH, k⟩ => ?_
  have fW : Frm (off q.B q.o) (k1Ranges l.W) s.mem t.mem :=
    (Frm.of_outside (ho₁.mono (o' := slot l.W aT) (n' := 8 * (l.W + 2)) (Nat.le_refl _) (by omega))
      (by simp [k1Ranges])).trans (by rw [← me₂]; exact hf)
  have fB : Frm q.B (shiftRanges q.o (k1Ranges l.W)) s.mem t.mem :=
    fW.rebase (by omega) fun r hr => by have := hk1 r hr; omega
  have kk := (k₁.trans k₂).trans k
  have hia' : word t.mem (off q.B q.o) (8 * sIfma) = off q.B q.a := by
    rw [fW.word_eq (fun r hr => by
      have := hdr_lt_slot l.W Public.aAcc (show sIfma < 32 by decide)
      have := hdr_lt_slot l.W Public.aTmp (show sIfma < 32 by decide)
      have := hdr_lt_slot l.W aT (show sIfma < 32 by decide)
      simp only [k1Ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only [sCtr, sIfma, sFn] at * <;> omega)
      (by unfold sIfma sFn; omega)]
    exact hia
  exact ⟨hok, mx, eb, TCtx.of_regionA hl hc hoa haZ hp hsp hsl hpv hlv he
    (fB.mono fun r hr => List.mem_append_left _ hr) kk.2.2 kk.2.1 ((kk.gpr (by decide)).trans hc.rdi) hH hia', hl'⟩

theorem k1_ct (hl : LayOk l) (hR : RegT l) {p sp sl : Nat} {rest : List (Prog isa)} (hr0 : rest ≠ [])
    (hr : RelCT isa (Two (RT l p sp sl)) (seqs rest) fun _ _ => True) :
    RelCT isa (Two (RegPre l p sp sl)) (seqs (k1 l ++ rest)) fun _ _ => True := by
  refine two_map id (fun _ _ h => k1_chain hl h) ?_
  simp only [k1, List.append_assoc, List.cons_append, List.nil_append]
  refine ct_steps (by simp [copyArr]) (by simp) (RegPub.pw l) (fun _ _ h => h.1) (fun _ _ h => h.2)
    (copyArr_ct (by decide) (by decide) (by taint_decide)) ?_
  obtain ⟨_, hcnt⟩ := hR.cnt
  refine ct_cons (List.cons_ne_nil _ _) (two_taint [.rdi] (pins_eqs (fun q _ => off q.B q.o)
    fun q s (h : K1 l p sp sl q s) r hr => by rw [List.mem_singleton.mp hr]; exact h.1) hcnt)
    (fun _ _ h => h.2) ?_
  exact ct_cons hr0 (two_map (fun q : RegPub => (q.pw l, l.dbls)) (fun _ _ h => h.1) (doublesW_ct (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide))) (fun _ _ h => h.2) hr

/-- The loads of `arr52`, for array `j`. -/
abbrev ArrLd (j : Nat) : Prop :=
  ∃ hc : VG.Taint.Hint VG.X86_64.Taint.T, (taint.check (Taint.ofRegs [.rdi]) (.block ([.mov .rsi (.mem (hdr (sArr j))),
    .mov .r11 (.mem (hdr sIfma))] : List Instr)) hc).isSome = true

theorem arrLd_aN : ArrLd Public.aN := ⟨_, by taint_decide⟩
theorem arrLd_aT : ArrLd aT := ⟨_, by taint_decide⟩
theorem arrLd_aXc : ArrLd aXc := ⟨_, by taint_decide⟩
theorem arrLd_aY : ArrLd Public.aY := ⟨_, by taint_decide⟩

theorem arr52_ct' (hl : LayOk l) {p j c sp sl : Nat} (hj : j < 8) (hc : c + l.NB ≤ l.D) (h₁ : ArrLd j)
    (hT : TOk [.rsi, .r11] (.block (arrTail l p c))) {rest : List (Prog isa)} (hr0 : rest ≠ [])
    (hr : RelCT isa (Two fun q s => RT l p sp sl q s ∧ s.gpr .r12 = mask52) (seqs rest) fun _ _ => True) :
    RelCT isa (Two (RT l p sp sl)) (seqs (.block (arr52 l p j c) :: rest)) fun _ _ => True :=
  let ⟨_, h₁⟩ := h₁
  ct_cons hr0 (arr52_ct hj h₁ hT) (fun _ _ h => arr52_rt hl hc hj h) hr

/-- `p`'s region is constant time. -/
theorem region0_ct (hl : LayOk l) {sp sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rax]) (.block [.mov .rsi (.mem (ws .rax sp)),
      .mov .rcx (.mem (ws .rax sl))]) hc).isSome = true) :
    RelCT isa (Two (RegPre l 0 sp sl)) (seqs (region l 0 sp sl)) fun _ _ => True := by
  have hR := regT hl
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hoM : oM = 0 := rfl
  have := NB_le hl
  have := E_pos hl
  rw [show region l 0 sp sl = k1 l ++ (.block (arr52 l 0 Public.aN oM) ::
    .block (arr52 l 0 aT l.oK1) :: .block (arr52 l 0 aXc l.oX) :: .block (arr52 l 0 Public.aY l.oY) ::
    .block (arr52 l 0 Public.aY l.oFin) :: .block (k0St l 0) :: .block (eZero l) ::
    eCopy l sp sl) from rfl]
  refine k1_ct hl hR (List.cons_ne_nil _ _) ?_
  refine arr52_ct' hl (by decide) (by omega) arrLd_aN hR.a0M (List.cons_ne_nil _ _) ?_
  refine two_map id (fun _ _ h => h.1) (arr52_ct' hl (by decide) (by omega) arrLd_aT hR.a0K1
    (List.cons_ne_nil _ _) ?_)
  refine two_map id (fun _ _ h => h.1) (arr52_ct' hl (by decide) (by omega) arrLd_aXc hR.a0X
    (List.cons_ne_nil _ _) ?_)
  refine two_map id (fun _ _ h => h.1) (arr52_ct' hl (by decide) (by omega) arrLd_aY hR.a0Y
    (List.cons_ne_nil _ _) ?_)
  refine two_map id (fun _ _ h => h.1) (arr52_ct' hl (by decide) (by omega) arrLd_aY hR.a0F
    (List.cons_ne_nil _ _) ?_)
  refine ct_cons (List.cons_ne_nil _ _) (k0St_ct 0 hR.k00) (fun _ _ h => k0St_rt hl h) ?_
  refine ct_cons (by simp [eCopy]) (eZero_ct 0 hR.eZ) (fun _ _ h => eZero_rt hl h) ?_
  exact two_map id (fun _ _ h => ⟨h.1, h.2.1⟩) (eCopy_ct hl hT hR.eEnd)

/-- `q`'s region is constant time. -/
theorem region1_ct (hl : LayOk l) {sp sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rax]) (.block [.mov .rsi (.mem (ws .rax sp)),
      .mov .rcx (.mem (ws .rax sl))]) hc).isSome = true) :
    RelCT isa (Two (RegPre l 1 sp sl)) (seqs (region l 1 sp sl)) fun _ _ => True := by
  have hR := regT hl
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hoM : oM = 0 := rfl
  have := NB_le hl
  have := E_pos hl
  rw [show region l 1 sp sl = k1 l ++ (.block (arr52 l 1 Public.aN oM) ::
    .block (arr52 l 1 aT l.oK1) :: .block (arr52 l 1 aXc l.oX) :: .block (arr52 l 1 Public.aY l.oY) ::
    .block (k0St l 1) :: .block (eZero l) :: .block (finOne l) :: eCopy l sp sl) from rfl]
  refine k1_ct hl hR (List.cons_ne_nil _ _) ?_
  refine arr52_ct' hl (by decide) (by omega) arrLd_aN hR.a1M (List.cons_ne_nil _ _) ?_
  refine two_map id (fun _ _ h => h.1) (arr52_ct' hl (by decide) (by omega) arrLd_aT hR.a1K1
    (List.cons_ne_nil _ _) ?_)
  refine two_map id (fun _ _ h => h.1) (arr52_ct' hl (by decide) (by omega) arrLd_aXc hR.a1X
    (List.cons_ne_nil _ _) ?_)
  refine two_map id (fun _ _ h => h.1) (arr52_ct' hl (by decide) (by omega) arrLd_aY hR.a1Y
    (List.cons_ne_nil _ _) ?_)
  refine ct_cons (List.cons_ne_nil _ _) (k0St_ct 1 hR.k01) (fun _ _ h => k0St_rt hl h) ?_
  refine ct_cons (List.cons_ne_nil _ _) (eZero_ct 1 hR.eZ) (fun _ _ h => eZero_rt hl h) ?_
  refine ct_cons (by simp [eCopy]) (finOne_ct hR.fin) (fun _ _ h => finOne_rt hl h) ?_
  exact eCopy_ct hl hT hR.eEnd

end VG.Proof.Bignum.X86_64.Ifma
