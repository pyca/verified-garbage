module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Ifma.Exp
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Ifma.Exp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPSub

/-!
# FFDH's exponentiation with AVX512_IFMA on x86-64: constant time

`expL_ct`: `expL`'s code leaks the same in runs with the same public data
(`EPre5`). Which layout runs, if any, depends only on the prime's size and
the exponent's length, which are public; each layout's pieces follow the
chain of `expW_chain`, each checked by the taint analysis (`region0_ct`,
`result_ct`, and the pieces here), and the loop it falls back to is
`crtExpLoop_ct`'s.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off)
open VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Impl.Ffdh.X86_64.Ifma
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Bignum.X86_64.Ifma
open VG.Proof.Bignum.X86_64.Ifma.Pub (PubOk PubOk.amm PubOk.nl)
open VG.Proof.MlKem.X86_64

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-! ## The blocks, in the pieces the taint analysis checks -/

/-- `head`'s loads of `sCtr` and of `n`'s base. -/
def headA : List Instr := [.mov .r8 (.mem (hdr sCtr)), .mov .rdx (.mem (hdr sLink))]

/-- `head`'s load of the exponent's length, through `n`'s base. -/
def headB (sl : Nat) : List Instr := [.mov .rcx (.mem (ws .rdx sl))]

/-- The rest of `head`. -/
def headC (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List Instr :=
  [.alu .add .rcx (.reg .rcx), .mov32 .rdx (.imm (BitVec.ofNat 32 (2 * l.P))), .alu .sub .rdx (.reg .rcx),
    .mov .rax (.reg .rdi), .alu .add .rax (.imm (BitVec.ofNat 32 (oArea l))), .store (hdr sIfma) .rax,
    .store (at_ .rax (oSt l)) .rdx, .store (at_ .rax (oSv l)) .r8]

theorem head_split (sl : Nat) : head l sl = headA ++ (headB sl ++ headC l) := rfl

/-- `fits`'s loads from the prime's header. -/
def fitsA (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List Instr :=
  [.mov .rax (.mem (hdr sW)), .alu .xor .rax (.imm (BitVec.ofNat 32 l.W)), .mov .rdx (.mem (hdr sLink))]

/-- `fits`'s load of the exponent's length, through `n`'s base. -/
def fitsB (sl : Nat) : List Instr := [.mov .rdx (.mem (ws .rdx sl))]

/-- The rest of `fits`. -/
def fitsC (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List Instr :=
  [.alu .cmp .rdx (.imm (BitVec.ofNat 32 (8 * l.W + 1))), .alu .sbb .rcx (.reg .rcx), .alu .add .rcx (.imm 1),
    .alu .or .rax (.reg .rcx)]

theorem fits_split (sl : Nat) : fits l sl = fitsA l ++ (fitsB sl ++ fitsC l) := rfl

/-- `tail`'s load of the area's base. -/
def tailA : List Instr := [.mov .rax (.mem (hdr sIfma))]

/-- The rest of `tail`. -/
def tailB (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List Instr :=
  [.mov .rcx (.mem (at_ .rax (oSv l))), .store (hdr sCtr) .rcx]

theorem tail_split : tail l = tailA ++ tailB l := rfl

/-- The taint checks that depend on the layout. -/
structure LT (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Prop where
  hc : TOk [.rdi] (.block (headC l))
  fa : TOk [.rdi] (.block (fitsA l))
  fc : TOk [] (.block (fitsC l))
  tb : TOk [.rdi, .rax] (.block (tailB l))
  vec : TOk [.rbx, .rbp] (Impl.Ffdh.X86_64.Ifma.vec l)
  bb : TOk [.rbx] (.block [.mov .rbp (.mem (at_ .rbx (oSt l)))])
  r0 : TOk [.rdi] (.block (resLd l 0))
  mid : TOk [.rdi, .r11, .r8] (.block (resMid l))

theorem lT (hl : PubOk l) : LT l := by
  rcases hl with rfl | rfl | rfl <;>
    exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

/-- Pins nothing. -/
theorem pins_nil {α : Type} {Φ : α → State → Prop} : Pins Φ [] := fun _ _ _ _ _ _ hr => absurd hr (by simp)

/-! ## `head` and `tail` -/

/-- After `headA`: `n`'s base in `rdx`. -/
def HA (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : BPub) (t : State) : Prop :=
  ∃ s, HPre l p s ∧ t.gpr .rdx = p.x.B ∧ t.gpr .rdi = s.gpr .rdi ∧ t.rd = s.rd ∧ t.wr = s.wr

theorem head_ct (sl : Nat) (hsl : sl < 32) (hT : TOk [.rdi] (.block (headC l)))
    (hB : TOk [.rdi, .rdx] (.block (headB sl))) :
    RelCT isa (Two (HPre l)) (.block (head l sl)) fun _ _ => True := by
  obtain ⟨_, hT⟩ := hT
  obtain ⟨_, hB⟩ := hB
  rw [head_split]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := HA l) [.rdi]
    (pins_eqs (fun p _ => off p.x.B p.x.o) fun p s h r hr => by rw [List.mem_singleton.mp hr]; exact h.2.1)
    (by taint_decide) ?_) (RelCT.block_append (RelCT.seq (two_piece (Ψ := fun p t => t.gpr .rdi = off p.x.B p.x.o)
      [.rdi, .rdx] (pins_eqs (fun p r => if r = .rdi then off p.x.B p.x.o else p.x.B) fun p t ⟨s, h, dx, di, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact di.trans h.2.1
        · exact dx) hB ?_)
      (two_taint [.rdi] (pins_eqs (fun p _ => off p.x.B p.x.o) fun p t h r hr => by
        rw [List.mem_singleton.mp hr]; exact h) hT))))
  · rintro p s h
    obtain ⟨hs, hdi, hlk, h32, hZ⟩ := h
    have hn := hs.nowrap
    have hld : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off p.x.B p.x.o) (8 * i)) 8 := fun i hi => by
      rw [off_off]; exact hs.ld (by have := hdr_lt_slot l.W 8 hi; omega_using [this, hZ])
    refine WP.mono (WP.keep [.r8, .rdx] (Q := fun t => t.gpr .rdx = p.x.B) (by
      unfold headA
      xrun [State.ea, hdr, hdi, hdrOff, hld sCtr (by decide), hld sLink (by decide), hlk]) rfl)
      fun t ⟨dx, k⟩ => ⟨s, ⟨hs, hdi, hlk, h32, hZ⟩, dx, k.gpr (by decide), k.2.1, k.2.2⟩
  · rintro p t ⟨s, ⟨hs, hdi, hlk, h32, hZ⟩, dx, di, rd, wr⟩
    have hn := hs.nowrap
    have hld : InRegions (t.rd ++ t.wr) (off p.x.B (8 * sl)) 8 := by
      rw [rd, wr]; exact hs.ld (by omega_using [hsl, h32, hZ])
    refine WP.mono (WP.keep [.rcx] (Q := fun _ => True) (by
      unfold headB
      xrun [State.ea, ws, dx, hdrOff, hld]; exact ⟨_, rfl⟩) rfl) fun u ⟨_, k⟩ => by rw [k.gpr (by decide), di, hdi]

/-- After `tailA`: the area's base in `rax`. -/
def TA (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : BPub) (t : State) : Prop :=
  t.gpr .rdi = off p.x.B p.x.o ∧ t.gpr .rax = off p.x.B (p.x.o + oArea l)

theorem tail_ct (hT : TOk [.rdi, .rax] (.block (tailB l))) :
    RelCT isa (Two (TPre l)) (.block (tail l)) fun _ _ => True := by
  obtain ⟨_, hT⟩ := hT
  rw [tail_split]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := TA l) [.rdi]
    (pins_eqs (fun p _ => off p.x.B p.x.o) fun p s h r hr => by rw [List.mem_singleton.mp hr]; exact h.2.1)
    (by taint_decide) ?_)
    (two_taint [.rdi, .rax] (pins_eqs (fun p r => if r = .rdi then off p.x.B p.x.o else off p.x.B (p.x.o + oArea l))
      fun p t h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) hT))
  rintro p s ⟨hs, hdi, hia, hoa, hZ⟩
  have hn := hs.nowrap
  have hld : InRegions (s.rd ++ s.wr) (off (off p.x.B p.x.o) (8 * sIfma)) 8 := by
    rw [off_off]
    exact hs.ld (by have := hdr_lt_slot l.W 8 (show sIfma < 32 by decide); omega_using [this, hoa, hZ])
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = off p.x.B (p.x.o + oArea l)) (by
    unfold tailA
    xrun [State.ea, hdr, hdi, hdrOff, hld, hia]) rfl) fun t ⟨ax, k⟩ => ⟨by rw [k.gpr (by decide), hdi], ax⟩

/-! ## The vector code -/

/-- After `bases`' first load: the area's base in `rbx`. -/
def BA (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : BPub) (t : State) : Prop :=
  ∃ s, VPreF l p s ∧ t.gpr .rbx = off p.x.B (p.x.o + oArea l) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr

/-- `bases`' first load. -/
theorem basesA_ok {p : BPub} {s : State} (h : VPreF l p s) :
    WP isa (.block [.mov .rbx (.mem (hdr sIfma))]) s (BA l p) := by
  have h' := h
  dsimp only [VPreF, VPre, vP] at h'
  obtain ⟨⟨hs, hdi, hia, ho⟩, -, -⟩ := h'
  have hn := hs.nowrap
  have hl : InRegions (s.rd ++ s.wr) (off (off p.x.B p.x.o) (8 * sIfma)) 8 := by
    rw [off_off]; exact hs.ld (by unfold sIfma sFn; omega_arith)
  exact WP.mono (WP.keep [.rbx] (Q := fun u => u.gpr .rbx = off p.x.B (p.x.o + oArea l) ∧ u.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hl, hia]) rfl) fun t ⟨⟨bx, me⟩, k⟩ => ⟨s, h, bx, me, k.2.1, k.2.2⟩

/-- `bases`' second load: the first digit. -/
theorem basesB_ok (hl : PubOk l) {p : BPub} {t : State} (h : BA l p t) :
    WP isa (.block [.mov .rbp (.mem (at_ .rbx (oSt l)))]) t fun u =>
      u.gpr .rbx = off p.x.B (p.x.o + oArea l) ∧ u.gpr .rbp = BitVec.ofNat 64 (2 * (l.P - p.len)) := by
  obtain ⟨s, hv, bx, me, rd, wr⟩ := h
  dsimp only [VPreF, VPre, vP] at hv
  obtain ⟨⟨hs, -, -, -⟩, hst, hZ⟩ := hv
  have hD := (PubOk.sizes hl).2.2.2.2.2.2.2.2.2.2.2.2
  have hSt := (PubOk.sizes hl).2.2.2.2.2.2.2.1
  have hn := hs.nowrap
  have eS : off p.x.B (p.x.o + oArea l) + BitVec.ofNat 64 (oSt l) = off p.x.B (p.x.o + oArea l + oSt l) :=
    off_off _ _ _
  have hld : InRegions (t.rd ++ t.wr) (off p.x.B (p.x.o + oArea l) + BitVec.ofNat 64 (oSt l)) 8 := by
    rw [eS, rd, wr]; exact hs.ld hZ
  have sS := AmmSym.se_ofNat (show oSt l < 2 ^ 31 by omega_using [hSt, hD])
  exact WP.mono (WP.keep [.rbp] (Q := fun u => u.gpr .rbp = BitVec.ofNat 64 (2 * (l.P - p.len))) (by
    xrun [State.ea, at_, eaG', BitVec.ofInt_natCast, bx, hld]
    rw [eS, me, show s.mem.readW (off p.x.B (p.x.o + oArea l + oSt l)) 64 =
      word s.mem p.x.B (p.x.o + oArea l + oSt l) from rfl, hst]) rfl)
    fun u ⟨bp, k⟩ => ⟨by rw [k.gpr (by decide)]; exact bx, bp⟩

/-- The bases, then the vector code: constant time, the first digit public. -/
theorem vecF_ct (hl : PubOk l) (hT : TOk [.rbx, .rbp] (Impl.Ffdh.X86_64.Ifma.vec l))
    (hB : TOk [.rbx] (.block [.mov .rbp (.mem (at_ .rbx (oSt l)))])) :
    RelCT isa (Two (VPreF l)) (seqs [.block (Impl.Ffdh.X86_64.Ifma.bases l), Impl.Ffdh.X86_64.Ifma.vec l])
      fun _ _ => True := by
  obtain ⟨_, hT⟩ := hT
  obtain ⟨_, hB⟩ := hB
  have hsplit : Impl.Ffdh.X86_64.Ifma.bases l =
      [.mov .rbx (.mem (hdr sIfma))] ++ [.mov .rbp (.mem (at_ .rbx (oSt l)))] := rfl
  have hb : RelCT isa (Two (VPreF l)) (.block (Impl.Ffdh.X86_64.Ifma.bases l)) (Two fun (p : BPub) t =>
      t.gpr .rbx = off p.x.B (p.x.o + oArea l) ∧ t.gpr .rbp = BitVec.ofNat 64 (2 * (l.P - p.len))) := by
    rw [hsplit]
    exact RelCT.block_append (RelCT.seq (two_piece (Ψ := BA l) [.rdi]
      (pins_eqs (fun p _ => off p.x.B p.x.o) fun p s h r hr => by rw [List.mem_singleton.mp hr]; exact h.1.2.1)
      (by taint_decide) fun _ _ h => basesA_ok h) (two_piece [.rbx]
        (pins_eqs (fun p _ => off p.x.B (p.x.o + oArea l)) fun p t h r hr => by
          rw [List.mem_singleton.mp hr]; exact h.choose_spec.2.1) hB fun _ _ h => basesB_ok hl h))
  exact RelCT.seq hb (two_taint [.rbx, .rbp] (pins_eqs (fun p r => if r = .rbx then off p.x.B (p.x.o + oArea l)
    else BitVec.ofNat 64 (2 * (l.P - p.len))) fun p t h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2) hT)

/-! ## A layout's exponentiation -/

/-- The chain from `head`, for some values only correctness needs. -/
def G0 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (sp sl : Nat) (p : BPub) (s : State) : Prop := ∃ g, C0 l sp sl p g s
def G1 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (sp sl : Nat) (p : BPub) (s : State) : Prop := ∃ g, C1 l sp sl p g s
def G2 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : BPub) (s : State) : Prop := ∃ g, C2 l p g s
def G3 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : BPub) (s : State) : Prop := ∃ g, C3 l p g s
def G4 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : BPub) (s : State) : Prop := ∃ g, C4 l p g s

/-- A layout's exponentiation is constant time along its chain. -/
theorem exp_ct (hl : PubOk l) {sp sl : Nat} (hsl : sl < 32) (hB : TOk [.rdi, .rdx] (.block (headB sl)))
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hR : (taint.check (Taint.ofRegs [.rax]) (.block [.mov .rsi (.mem (ws .rax sp)),
      .mov .rcx (.mem (ws .rax sl))]) hc).isSome = true) :
    RelCT isa (Two (G0 l sp sl)) (seqs (exp l sp sl)) fun _ _ => True := by
  have hL := lT hl
  rw [exp_eq]
  refine ct_cons (by simp [region]) (two_map id (fun _ _ ⟨_, h⟩ => h.1) (head_ct sl hsl hL.hc hB))
    (Ψ := G1 l sp sl) (fun _ _ ⟨g, h⟩ => WP.mono h.2 fun _ h' => ⟨g, h'⟩) ?_
  refine ct_steps (c := region l 0 sp sl) (by simp [region, k1, copyArr]) (by simp) (regP l) (fun _ _ ⟨_, h⟩ => h.1)
    (Ψ := G2 l) (fun _ _ ⟨g, h⟩ => WP.mono h.2 fun _ h' => ⟨g, h'⟩) (region0_ct hl.amm hR) ?_
  refine ct_steps (c := [.block (Impl.Ffdh.X86_64.Ifma.bases l), Impl.Ffdh.X86_64.Ifma.vec l]) (by simp)
    (by simp [result]) id (fun _ _ ⟨_, h⟩ => h.1) (Ψ := G3 l)
    (fun _ _ ⟨g, h⟩ => WP.mono h.2 fun _ h' => ⟨g, h'⟩) (vecF_ct hl hL.vec hL.bb) ?_
  exact ct_steps (c := result l 0) (by simp [result]) (by simp) (resP l) (fun _ _ ⟨_, h⟩ => h.1) (Ψ := G4 l)
    (fun _ _ ⟨g, h⟩ => WP.mono h.2 fun _ h' => ⟨g, h'⟩) (result_ct hl.amm 0 hL.r0 hL.mid)
    (two_map id (fun _ _ ⟨_, h⟩ => h.1) (tail_ct hL.tb))

/-! ## The dispatch -/

/-- `EPre5` after code that writes only `rax`, `rcx` and `rdx`. -/
theorem EPre5.keep {sp sl : Nat} {p : BPub} {s t : State} (h : EPre5 sp sl p s) (hm : t.mem = s.mem)
    (hk : Keep [.rax, .rcx, .rdx] s t) : EPre5 sp sl p t := by
  obtain ⟨⟨minv, X, x, y, eb, hc, hw2, hwx, hw30, hn, hinv, hodd, hxl, hxc, hyl, hyc, hsp, hsl, hep, hel, hlen,
    hL1, hL2, he⟩, hT⟩ := h
  rw [← hm] at hn hinv hxl hxc hyl hyc hep hel
  exact ⟨⟨minv, X, x, y, eb, SubCtx.of_frmW hc hT (rs := []) (fun x _ => by rw [hm]) (by simp) hk.2.2
    (hk.gpr (by decide)), hw2, hwx, hw30, hn, hinv, hodd, hxl, hxc, hyl, hyc, hsp, hsl, hep, hel, hlen, hL1, hL2,
    he.congr (fun x _ => by rw [hm]) hk.2.1 hk.2.2⟩, hT⟩

/-- After `fits`: whether the layout fits, in ZF. -/
def FP (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (sp sl : Nat) (p : BPub) (t : State) : Prop :=
  EPre5 sp sl p t ∧ t.zf = some (decide (p.x.wx = l.W ∧ p.len ≤ 8 * l.W))

/-- After `fitsA`: `n`'s base in `rdx`. -/
def FA (sp sl : Nat) (p : BPub) (t : State) : Prop :=
  ∃ s, EPre5 sp sl p s ∧ t.gpr .rdx = p.x.B ∧ t.gpr .rdi = s.gpr .rdi ∧ t.rd = s.rd ∧ t.wr = s.wr

theorem fitsA_ok {sp sl : Nat} {p : BPub} {s : State} (h : EPre5 sp sl p s) :
    WP isa (.block (fitsA l)) s (FA sp sl p) := by
  have h' := h
  obtain ⟨⟨minv, X, x, y, eb, hc, -⟩, hT⟩ := h'
  have hs := hc.scr
  have hn := hs.nowrap
  have hld : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off p.x.B p.x.o) (8 * i)) 8 := fun i hi => by
    rw [off_off]
    exact hs.ld (by have := hdr_lt_slot p.x.wx 8 hi; unfold wsTab tabBytes at hT; omega_using [this, hT])
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.gpr .rdx = p.x.B) (by
    unfold fitsA
    xrun [State.ea, hdr, hc.rdi, hdrOff, hld sW (by decide), hld sLink (by decide), hc.link]) rfl)
    fun t ⟨dx, k⟩ => ⟨s, h, dx, k.gpr (by decide), k.2.1, k.2.2⟩

theorem fitsB_ok {sp sl : Nat} {p : BPub} {t : State} (h : FA sp sl p t) :
    WP isa (.block (fitsB sl)) t fun _ => True := by
  obtain ⟨s, ⟨⟨minv, X, x, y, eb, hc, -, -, -, -, -, -, -, -, -, -, -, hsl, -⟩, hT⟩, dx, -, rd, wr⟩ := h
  have hs := hc.scr
  have hlo := hc.lo
  have hw8 := hdr_lt_slot p.x.w 8 hsl
  have hld : InRegions (t.rd ++ t.wr) (off p.x.B (8 * sl)) 8 := by
    rw [rd, wr]; exact hs.ld (by omega_using [hw8, hlo, hT])
  unfold fitsB
  xrun [State.ea, ws, dx, hdrOff, hld]
  exact ⟨_, rfl⟩

/-- `fits` leaks the same in runs with the same public data, and leaves ZF as `FP` says. -/
theorem fits_ct (hl : PubOk l) {sp sl : Nat} (hB : TOk [.rdi, .rdx] (.block (fitsB sl))) :
    RelCT isa (Two (EPre5 sp sl)) (.block (fits l sl)) (Two (FP l sp sl)) := by
  have hL := lT hl
  obtain ⟨_, hA⟩ := hL.fa
  obtain ⟨_, hC⟩ := hL.fc
  obtain ⟨_, hB⟩ := hB
  have hW := (PubOk.sizes hl).2.2.2.2.2.2.2.2.2.2.1
  refine two_post ?_ fun p s h => ?_
  · rw [fits_split]
    exact RelCT.block_append (RelCT.seq (two_piece (Ψ := FA sp sl) [.rdi]
      (pins_eqs (fun p _ => off p.x.B p.x.o) fun p s h r hr => by
        obtain ⟨⟨_, _, _, _, _, hc, -⟩, -⟩ := h; rw [List.mem_singleton.mp hr]; exact hc.rdi) hA
      fun _ _ h => fitsA_ok h)
      (RelCT.block_append (RelCT.seq (two_piece (Ψ := fun _ _ => True) [.rdi, .rdx]
        (pins_eqs (fun p r => if r = .rdi then off p.x.B p.x.o else p.x.B) fun p t h r hr => by
          obtain ⟨s, ⟨⟨_, _, _, _, _, hc, -⟩, -⟩, dx, di, -⟩ := h
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact di.trans hc.rdi
          · exact dx) hB fun _ _ h => fitsB_ok h)
        (two_taint [] pins_nil hC))))
  · have h' := h
    obtain ⟨⟨minv, X, x, y, eb, hc, hw2, hwx, hw30, -, -, -, -, -, -, -, -, hsl, -, hel, hlen, -, hL2, -⟩, -⟩ := h'
    exact WP.mono (fits_ok hc hsl hel (by omega_using [hL2]) (by omega_using [hwx, hw30]) (by omega_using [hW]))
      fun t ⟨m, z, k⟩ => ⟨EPre5.keep h m k, by rw [z, hlen]⟩

/-- When the layout fits, the chain from `head`. -/
theorem g0_of (hl : PubOk l) {sp sl : Nat} {p : BPub} {s : State} (h : FP l sp sl p s)
    (hz : isa.eval .e s = some true) : G0 l sp sl p s := by
  obtain ⟨⟨⟨minv, X, x, y, eb, hc, hw2, hwx, hw30, hn, hinv, hodd, hxl, hxc, hyl, hyc, hsp, hsl, hep, hel, hlen,
    hL1, hL2, he⟩, hT⟩, z⟩ := h
  have hf : p.x.wx = l.W ∧ p.len ≤ 8 * l.W := by
    have : s.zf = some true := hz
    rw [this] at z
    exact of_decide_eq_true (Option.some.inj z).symm
  obtain ⟨⟨B, Z, o, w, wx⟩, ptr, len⟩ := p
  obtain ⟨hwW, hLW⟩ := hf
  simp only at hwW hLW hlen hc hT hn hinv hxl hxc hyl hyc hep hel he
  subst hwW hlen
  exact ⟨_, expW_chain hl (Q := False) (x := 0) hc hT hn hinv hodd hxl (fun h => h.elim) hyl (fun h => h.elim) hsp hsl hep hel
    hL1 hLW he⟩

/-- A layout's vector code if it fits, else `rest`: constant time. -/
theorem disp_ct (hl : PubOk l) {sp sl : Nat} (hsl : sl < 32) (hF : TOk [.rdi, .rdx] (.block (fitsB sl)))
    (hH : TOk [.rdi, .rdx] (.block (headB sl))) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hR : (taint.check (Taint.ofRegs [.rax]) (.block [.mov .rsi (.mem (ws .rax sp)),
      .mov .rcx (.mem (ws .rax sl))]) hc).isSome = true)
    {rest : Prog isa} (hr : RelCT isa (Two (EPre5 sp sl)) rest fun _ _ => True) :
    RelCT isa (Two (EPre5 sp sl)) (.seq (.block (fits l sl)) (.ite .e (seqs (exp l sp sl)) rest))
      fun _ _ => True :=
  RelCT.seq (fits_ct hl hF) (two_ite (fun _ _ _ h₁ h₂ => by
      show _root_.VG.X86_64.State.zf _ = _root_.VG.X86_64.State.zf _; rw [h₁.2, h₂.2])
    (two_map id (fun _ _ h => g0_of hl h.1 h.2) (exp_ct hl hsl hH hR))
    (two_map id (fun _ _ h => h.1.1) hr))

/-- FFDH's exponentiation with AVX512_IFMA is constant time, given the
taint checks of the code that depends on the exponent's slots. -/
theorem expL_ct (M : Mont) {sp sl : Nat} (hsl : sl < 32) (hF : TOk [.rdi, .rdx] (.block (fitsB sl)))
    (hH : TOk [.rdi, .rdx] (.block (headB sl))) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hR : (taint.check (Taint.ofRegs [.rax]) (.block [.mov .rsi (.mem (ws .rax sp)),
      .mov .rcx (.mem (ws .rax sl))]) hc).isSome = true) {hc' : VG.Taint.Hint VG.X86_64.Taint.T}
    (hW : (taint.check (Taint.ofRegs [.rdi, .rax]) (.block [.mov .rdx (.mem (Crt.ws .rax sp)),
      .store (hdr Crt.sExp) .rdx, .mov .rdx (.mem (Crt.ws .rax sl)), .store (hdr Crt.sExpLen) .rdx,
      .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx]) hc').isSome = true) :
    ExpCTL (expL M) sp sl :=
  disp_ct (.inl rfl) hsl hF hH hR (disp_ct (.inr (.inl rfl)) hsl hF hH hR (disp_ct (.inr (.inr rfl)) hsl hF hH hR
    (two_map id (fun _ _ h => h.1) (crtExpLoop_ct M CrtSel.sse CrtSel.sse_ct hW))))

end VG.Proof.Ffdh.X86_64.Ifma
