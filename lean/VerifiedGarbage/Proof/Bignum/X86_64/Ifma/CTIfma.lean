import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTRegion
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTLemmas

/-!
# RSA with AVX512_IFMA on x86-64, any size: constant time, `ifma`

`ifma`'s blocks read pointers from the
workspaces' headers, which are the same in two runs with the same public
data; the taint analysis checks each block after its loads, whose results
correctness gives (the head block, `head_ct`; the moves between the
workspaces, `swap_ct`; the results, `result_ct`). The vector code's
addresses all come from `rbx`, the area's base (`vecB_ct`). With the regions
(`region0_ct`, `region1_ct`), `ifma` is constant time (`ifma_ct`) for
`ifma_ok`'s hypotheses. The checks of the code that depends on the layout
are `IfT l`, which `ifT` evaluates for each layout.
-/

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64 (ct_split pins_eqs ct_cons SwPre swap_ct swPre_of two)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-! ## The taint checks of the code that depends on the layout -/

/-- `result p`'s first loads. -/
def resLd (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : Nat) : List Instr :=
  [.mov .r11 (.mem (hdr sIfma)), .alu .add .r11 (.imm (BitVec.ofNat 32 (l.D * p + l.oY))),
    .mov .r8 (.mem (hdr (sArr Public.aAcc)))]

/-- `result`'s conversion and the subtraction's bases. -/
def resMid (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List Instr :=
  to64 l ++ ([.mov .rbx (.mem (hdr (sArr Public.aY))), .mov .r10 (.mem (hdr (sArr Public.aN))),
    .mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr Public.aTmp)))] : List Instr)

/-- `ifma`'s checks that depend on the layout, but the regions'. -/
structure IfT (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Prop where
  vec : TOk [.rbx] (vec l)
  r0 : TOk [.rdi] (.block (resLd l 0))
  r1 : TOk [.rdi] (.block (resLd l 1))
  mid : TOk [.rdi, .r11, .r8] (.block (resMid l))

theorem ifT (hl : LayOk l) : IfT l := by
  rcases hl with rfl | rfl | rfl <;>
    exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

/-! ## The head block -/

/-- The public data of the head: `n`'s workspace, the primes' (of `wx`
words) and the size `A` of the area. -/
structure HdPub where
  B : Addr
  Z : Nat
  w : Nat
  op : Nat
  oq : Nat
  wx : Nat
  A : Nat

/-- `ifmaHead_ok`'s hypotheses. -/
def HdPre (p : HdPub) (s : State) : Prop :=
  ∃ (minv mq : BitVec 64), VG.Proof.Bignum.X86_64.Good s p.B p.Z p.w minv ∧ slot p.w 8 ≤ p.op ∧
    p.op + slot p.wx 8 + tabBytes p.wx ≤ p.oq ∧ p.oq + slot p.wx 8 + tabBytes p.wx + p.A ≤ p.Z ∧
    word s.mem p.B (8 * sWsP) = off p.B p.op ∧ word s.mem p.B (8 * sWsQ) = off p.B p.oq ∧ WsAt s.mem p.B p.oq p.wx mq

/-- After `q`'s base is loaded. -/
def HdA (p : HdPub) (t : State) : Prop :=
  ∃ s, HdPre p s ∧ t.gpr .rdx = off p.B p.oq ∧ t.mem = s.mem ∧ Keep [.rdx] s t

/-- After the area's base is computed and `p`'s base loaded. -/
def HdB (p : HdPub) (t : State) : Prop :=
  ∃ s, HdPre p s ∧ t.gpr .rdx = off p.B p.op ∧ t.gpr .rax = off (off p.B p.oq) (slot p.wx 8 + tabBytes p.wx) ∧
    t.mem = s.mem ∧ Keep [.rax, .rdx] s t

/-- After the store into `p`'s workspace, and `q`'s base loaded again. -/
def HdC (p : HdPub) (t : State) : Prop :=
  ∃ s, HdPre p s ∧ t.gpr .rdx = off p.B p.oq ∧ t.gpr .rax = off (off p.B p.oq) (slot p.wx 8 + tabBytes p.wx) ∧
    t.mem = s.mem.writeW (off (off p.B p.op) (8 * sIfma)) (off (off p.B p.oq) (slot p.wx 8 + tabBytes p.wx)) ∧
    Keep [.rax, .rdx] s t

theorem head_eq : (([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ wsEndT ++
    ([.mov .rdx (.mem (hdr sWsP)), .store (ws .rdx sIfma) .rax, .mov .rdx (.mem (hdr sWsQ)),
      .store (ws .rdx sIfma) .rax, enterP] : List Instr)) =
    ([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ ((wsEndT ++ ([.mov .rdx (.mem (hdr sWsP))] : List Instr)) ++
      (([.store (ws .rdx sIfma) .rax, .mov .rdx (.mem (hdr sWsQ))] : List Instr) ++
        ([.store (ws .rdx sIfma) .rax, enterP] : List Instr))) := by
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- Pins `rdi` (`n`'s base) and `rdx` from a predicate after the head's start. -/
theorem pins_hd {Φ : HdPub → State → Prop} (f : HdPub → Addr)
    (h : ∀ p t, Φ p t → ∃ s, HdPre p s ∧ t.gpr .rdx = f p ∧ t.gpr .rdi = s.gpr .rdi) :
    Pins Φ [.rdi, .rdx] :=
  pins_eqs (fun p r => if r = .rdi then p.B else f p) fun p t h' r hr => by
    obtain ⟨s, ⟨_, _, hg, _⟩, hdx, hdi⟩ := h p t h'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hdi.trans hg.rdi
    · exact hdx

/-- The head block is constant time. -/
theorem head_ct : RelCT isa (Two HdPre) (.block (([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ wsEndT ++
    ([.mov .rdx (.mem (hdr sWsP)), .store (ws .rdx sIfma) .rax, .mov .rdx (.mem (hdr sWsQ)),
      .store (ws .rdx sIfma) .rax, enterP] : List Instr))) fun _ _ => True := by
  rw [head_eq]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := HdA) [.rdi]
    (pins_eqs (fun p _ => p.B) fun p s h r hr => by
      obtain ⟨_, _, hg, _⟩ := h; rw [List.mem_singleton.mp hr]; exact hg.rdi) (by taint_decide) ?_)
    (RelCT.block_append (RelCT.seq (two_piece (Ψ := HdB) [.rdi, .rdx]
      (pins_hd (fun p => off p.B p.oq) fun p t ⟨s, h, dx, _, k⟩ => ⟨s, h, dx, k.gpr (by decide)⟩) (by taint_decide) ?_)
      (RelCT.block_append (RelCT.seq (two_piece (Ψ := HdC) [.rdi, .rdx]
        (pins_hd (fun p => off p.B p.op) fun p t ⟨s, h, dx, _, _, k⟩ => ⟨s, h, dx, k.gpr (by decide)⟩)
        (by taint_decide) ?_)
        (two_taint [.rdi, .rdx] (pins_hd (fun p => off p.B p.oq) fun p t ⟨s, h, dx, _, _, k⟩ =>
          ⟨s, h, dx, k.gpr (by decide)⟩) (by taint_decide)))))))
  · rintro p s h
    have h' := h
    obtain ⟨minv, mq, hg, hlo, hpq, haZ, hsp, hsq, hwsq⟩ := h'
    have hn := hg.scr.nowrap
    have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
    refine WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = off p.B p.oq ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (d := 8 * sWsQ) (by unfold sWsQ sFn; omega), hsq]) rfl)
      fun t ⟨⟨dx, me⟩, k⟩ => ⟨s, h, dx, me, k⟩
  · rintro p t ⟨s, h, dx, me, k⟩
    have h' := h
    obtain ⟨minv, mq, hg, hlo, hpq, haZ, hsp, hsq, hwsq⟩ := h'
    have hs := hg.scr
    have hn := hs.nowrap
    have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
    have h16 := hdr_lt_slot p.wx 8 (show 31 < 32 by decide)
    rw [WP.block_append_iff]
    refine WP.mono (wsEndT_ok (X := off p.B p.oq) (Z := slot p.wx 8 + tabBytes p.wx) (wx := p.wx)
      ((hs.congr k.2.2).sub (by omega) (by omega)) dx (by rw [me]; exact hwsq.hdr.hw)
      (by rw [me]; exact hwsq.hdr.harr _ (by decide)) (by omega)) fun t₂ ⟨ax₂, me₂, k₂⟩ => ?_
    have k12 := k.trans k₂
    have hdi₂ : t₂.gpr .rdi = p.B := by rw [k12.gpr (by decide)]; exact hg.rdi
    refine WP.mono (WP.keep [.rdx] (Q := fun u => u.gpr .rdx = off p.B p.op ∧ u.mem = t₂.mem) (by
      xrun [State.ea, hdr, hdi₂, hdrOff, (hs.congr k12.2.2).ld (d := 8 * sWsP) (by unfold sWsP sFn; omega)]
      rw [me₂, me]; exact hsp) rfl) fun u ⟨⟨dx', me'⟩, k'⟩ =>
        ⟨s, h, dx', by rw [k'.gpr (by decide)]; exact ax₂, me'.trans (me₂.trans me), (k12.trans k').mono (by simp)⟩
  · rintro p t ⟨s, h, dx, ax, me, k⟩
    have h' := h
    obtain ⟨minv, mq, hg, hlo, hpq, haZ, hsp, hsq, hwsq⟩ := h'
    have hs := hg.scr
    have hn := hs.nowrap
    have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
    have h16 := hdr_lt_slot p.wx 8 (show 31 < 32 by decide)
    have hdi : t.gpr .rdi = p.B := by rw [k.gpr (by decide)]; exact hg.rdi
    have hst : InRegions t.wr (off (off p.B p.op) (8 * sIfma)) 8 := by
      rw [k.2.2, off_off]; exact hs.st (by unfold sIfma sFn; omega)
    have hq' : (s.mem.writeW (off (off p.B p.op) (8 * sIfma)) (off (off p.B p.oq) (slot p.wx 8 + tabBytes p.wx))).readW
        (off p.B (8 * sWsQ)) 64 = off p.B p.oq := by
      rw [off_off]
      have := (writeW_outside s.mem p.B (d := p.op + 8 * sIfma) (off (off p.B p.oq) (slot p.wx 8 + tabBytes p.wx))
        (by unfold sIfma sFn; omega)).word (d := 8 * sWsQ) (.inl (by unfold sWsQ sFn; omega))
        (by unfold sWsQ sFn; omega)
      exact this.trans hsq
    have hl : InRegions (t.rd ++ t.wr) (off p.B (8 * sWsQ)) 8 := by
      rw [k.2.1, k.2.2]; exact hs.ld (by unfold sWsQ sFn; omega)
    refine WP.mono (WP.keep [.rdx] (Q := fun u => u.gpr .rdx = off p.B p.oq ∧
      u.mem = s.mem.writeW (off (off p.B p.op) (8 * sIfma)) (off (off p.B p.oq) (slot p.wx 8 + tabBytes p.wx))) (by
        xrun [State.ea, hdr, ws, hdi, dx, ax, me, hdrOff, hst, hl, hq']) rfl) fun u ⟨⟨dx', me'⟩, k'⟩ =>
      ⟨s, h, dx', by rw [k'.gpr (by decide)]; exact ax, me', (k.trans k').mono (by simp)⟩

/-! ## The vector code -/

/-- In `q`'s workspace, the area's base in its header. -/
def VPre (p : Addr × Nat × Nat × Nat) (s : State) : Prop :=
  Scr s p.1 p.2.1 ∧ s.gpr .rdi = off p.1 p.2.2.1 ∧ word s.mem (off p.1 p.2.2.1) (8 * sIfma) = off p.1 p.2.2.2 ∧
    p.2.2.1 + 8 * 32 ≤ p.2.1

theorem vPre_of {B : Addr} {Z o a : Nat} {s : State} (hs : Scr s B Z) (hdi : s.gpr .rdi = off B o)
    (hia : word s.mem (off B o) (8 * sIfma) = off B a) (ho : o + 8 * 32 ≤ Z) : VPre (B, Z, o, a) s :=
  ⟨hs, hdi, hia, ho⟩

/-- The area's base into `rbx`, and the vector code: constant time. -/
theorem vecB_ct (hT : TOk [.rbx] (vec l)) :
    RelCT isa (Two VPre) (seqs [.block [.mov .rbx (.mem (hdr sIfma))], vec l]) fun _ _ => True := by
  obtain ⟨_, hT⟩ := hT
  exact RelCT.seq (two_piece (Ψ := fun p t => t.gpr .rbx = off p.1 p.2.2.2) [.rdi]
    (pins_eqs (fun p _ => off p.1 p.2.2.1) fun p s h r hr => by rw [List.mem_singleton.mp hr]; exact h.2.1)
    (by taint_decide) fun p s ⟨hs, hdi, hia, ho⟩ => by
      have hn := hs.nowrap
      have hl : InRegions (s.rd ++ s.wr) (off (off p.1 p.2.2.1) (8 * sIfma)) 8 := by
        rw [off_off]; exact hs.ld (by unfold sIfma sFn; omega)
      exact WP.mono (WP.keep [.rbx] (Q := fun u => u.gpr .rbx = off p.1 p.2.2.2) (by
        xrun [State.ea, hdr, hdi, hdrOff, hl, hia]) rfl) fun t h => h.1)
    (two_taint [.rbx] (pins_eqs (fun p _ => off p.1 p.2.2.2) fun p s h r hr => by
      rw [List.mem_singleton.mp hr]; exact h) hT)

/-! ## The results -/

/-- The public data of a result: `n`'s workspace, the prime's and the area. -/
structure ResPub where
  B : Addr
  Z : Nat
  o : Nat
  a : Nat

/-- `resBlock_ok`'s hypotheses. -/
def ResPre (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : Nat) (q : ResPub) (s : State) : Prop :=
  ∃ mx : BitVec 64, Scr s q.B q.Z ∧ s.gpr .rdi = off q.B q.o ∧ Hdr s.mem (off q.B q.o) l.W mx ∧
    word s.mem (off q.B q.o) (8 * sIfma) = off q.B q.a ∧ q.o + slot l.W 8 + tabBytes l.W ≤ q.a ∧
    q.a + 2 * l.D + 8 ≤ q.Z ∧ p < 2 ∧ (∀ j < l.L, limb l s.mem (off q.B q.a) (l.D * p + l.oY) j < 2 ^ 52) ∧
    val52 l s.mem (off q.B q.a) (l.D * p + l.oY) < 2 * wv s.mem (off q.B q.o) (slot l.W Public.aN) l.W

/-- The bases of the subtraction. -/
def ResRegs (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (q : ResPub) (t : State) : Prop :=
  t.gpr .r8 = off (off q.B q.o) (slot l.W Public.aAcc) ∧ t.gpr .rbx = off (off q.B q.o) (slot l.W Public.aY) ∧
    t.gpr .r10 = off (off q.B q.o) (slot l.W Public.aN) ∧ t.gpr .r12 = BitVec.ofNat 64 l.W ∧
    t.gpr .rsi = off (off q.B q.o) (slot l.W Public.aTmp)

theorem result_eq (p : Nat) : result l p = [.block (resLd l p ++ resMid l), subMod, selectAcc] := by
  simp only [result, resLd, resMid, List.cons_append, List.nil_append]

/-- `result p` is constant time, given the taint checks of its code that depends on the layout. -/
theorem result_ct (hl : LayOk l) (p : Nat) (hT : TOk [.rdi] (.block (resLd l p)))
    (hM : TOk [.rdi, .r11, .r8] (.block (resMid l))) :
    RelCT isa (Two (ResPre l p)) (seqs (result l p)) fun _ _ => True := by
  rw [result_eq]
  obtain ⟨_, hT⟩ := hT
  obtain ⟨_, hM⟩ := hM
  refine RelCT.seq (two_post (Ψ := ResRegs l) (ct_split _ _ [.rdi] [.rdi, .r11, .r8]
    (Ψ := fun q t => t.gpr .rdi = off q.B q.o ∧ t.gpr .r11 = off (off q.B q.a) (l.D * p + l.oY) ∧
      t.gpr .r8 = off (off q.B q.o) (slot l.W Public.aAcc))
    (pins_eqs (fun q _ => off q.B q.o) fun q s h r hr => by
      obtain ⟨_, _, hdi, _⟩ := h; rw [List.mem_singleton.mp hr]; exact hdi) hT ?_
    (pins_eqs (fun q r => if r = .rdi then off q.B q.o else if r = .r11 then off (off q.B q.a) (l.D * p + l.oY) else
      off (off q.B q.o) (slot l.W Public.aAcc)) fun q s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2) hM) ?_)
    (two_taint [.r8, .rbx, .r10, .r12, .rsi] (pins_eqs (fun q r => if r = .r8 then off (off q.B q.o) (slot l.W Public.aAcc)
      else if r = .rbx then off (off q.B q.o) (slot l.W Public.aY) else if r = .r10 then
        off (off q.B q.o) (slot l.W Public.aN) else if r = .r12 then BitVec.ofNat 64 l.W else
          off (off q.B q.o) (slot l.W Public.aTmp)) fun q s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2.1
        · exact h.2.2.2.2) (by taint_decide))
  · rintro q s ⟨mx, hs, hdi, hH, hia, hoa, haZ, hp, -⟩
    have hn := hs.nowrap
    obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
    obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
    have hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega
    have h8 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
    have hH' : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off q.B q.o) (8 * i)) 8 := fun i hi => by
      rw [off_off]; exact hs.ld (by have := hdr_lt_slot l.W 8 hi; omega)
    refine WP.mono (WP.keep [.r11, .r8] (Q := fun t => t.gpr .r11 = off (off q.B q.a) (l.D * p + l.oY) ∧
      t.gpr .r8 = off (off q.B q.o) (slot l.W Public.aAcc)) (by
      xrun [resLd, State.ea, hdr, hdi, hdrOff, hH' sIfma (by decide), hH' (sArr Public.aAcc) (by decide),
        AmmSym.se_ofNat (show l.D * p + l.oY < 2 ^ 31 by omega)]
      and_intros
      · rw [show s.mem.readW (off (off q.B q.o) (8 * sIfma)) 64 = off q.B q.a from hia]
      · exact hH.harr _ (by decide)) rfl) fun t ⟨⟨h11, h8'⟩, k⟩ => ⟨(k.gpr (by decide)).trans hdi, h11, h8'⟩
  · rintro q s ⟨mx, hs, hdi, hH, hia, hoa, haZ, hp, hL, hV⟩
    have := resBlock_ok hl hs hdi hH hia hoa haZ hp hL hV
    simp only [resLd, resMid, List.append_assoc] at this ⊢
    exact WP.mono this fun t ⟨_, _, r8, bx, r10, r12, si, _⟩ => ⟨r8, bx, r10, r12, si⟩

/-! ## `ifma` -/

/-- The public data of `ifma`: `n`'s workspace, the primes', the area, and
the exponents' pointers and lengths. -/
structure IfPub where
  B : Addr
  Z : Nat
  w : Nat
  op : Nat
  oq : Nat
  a : Nat
  ep : Addr
  eq : Addr
  lp : Nat
  lq : Nat

/-- `ifma_ok`'s hypotheses, but the values' (which the constant time does not need). -/
def IfPre (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : IfPub) (s : State) : Prop :=
  ∃ (minv mp mq mk : BitVec 64) (P Q : Nat) (ebp ebq : List Byte), Scr s p.B p.Z ∧ s.gpr .rdi = p.B ∧
    IPre l s.mem p.B p.w p.op p.oq minv mp mq mk P Q p.ep p.eq ebp.length ebq.length ∧ slot p.w 8 ≤ p.op ∧
    p.op + slot l.W 8 + tabBytes l.W ≤ p.oq ∧ p.a = p.oq + slot l.W 8 + tabBytes l.W ∧ p.a + 2 * l.D + 8 ≤ p.Z ∧
    P % 2 = 1 ∧ Q % 2 = 1 ∧ wv s.mem (off p.B p.op) (slot l.W Public.aY) l.W < P ∧
    wv s.mem (off p.B p.oq) (slot l.W Public.aY) l.W < Q ∧ wv s.mem (off p.B p.op) (slot l.W aXc) l.W < P ∧
    wv s.mem (off p.B p.oq) (slot l.W aXc) l.W < Q ∧ Src s p.B p.Z p.ep ebp ∧ Src s p.B p.Z p.eq ebq ∧
    1 ≤ ebp.length ∧ ebp.length ≤ l.E ∧ 1 ≤ ebq.length ∧ ebq.length ≤ l.E ∧ ebp.length = p.lp ∧ ebq.length = p.lq

/-- Before the last `leave`. -/
def F8 (p : IfPub) (t : State) : Prop := t.gpr .rdi = off p.B p.op

/-- Before `p`'s result. -/
def F7 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : IfPub) (t : State) : Prop :=
  ResPre l 0 ⟨p.B, p.Z, p.op, p.a⟩ t ∧ WP isa (seqs (result l 0)) t (F8 p)

/-- Before the move to `p`'s workspace. -/
def F6 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : IfPub) (t : State) : Prop :=
  SwPre (p.B, p.oq, p.Z) t ∧ WP isa (.block [leave, enterP]) t (F7 l p)

/-- Before `q`'s result. -/
def F5 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : IfPub) (t : State) : Prop :=
  ResPre l 1 ⟨p.B, p.Z, p.oq, p.a⟩ t ∧ WP isa (seqs (result l 1)) t (F6 l p)

/-- Before the vector code. -/
def F4 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : IfPub) (t : State) : Prop :=
  VPre (p.B, p.Z, p.oq, p.a) t ∧ WP isa (seqs [.block [.mov .rbx (.mem (hdr sIfma))], vec l]) t (F5 l p)

/-- Before `q`'s region. -/
def F3 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : IfPub) (t : State) : Prop :=
  RegPre l 1 sDq sQlen ⟨p.B, p.Z, p.oq, p.a, p.eq, p.lq⟩ t ∧ WP isa (seqs (region l 1 sDq sQlen)) t (F4 l p)

/-- Before the move to `q`'s workspace. -/
def F2 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : IfPub) (t : State) : Prop :=
  SwPre (p.B, p.op, p.Z) t ∧ WP isa (.block [leave, enterQ]) t (F3 l p)

/-- Before `p`'s region. -/
def F1 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : IfPub) (t : State) : Prop :=
  RegPre l 0 sDp sPlen ⟨p.B, p.Z, p.op, p.a, p.ep, p.lp⟩ t ∧ WP isa (seqs (region l 0 sDp sPlen)) t (F2 l p)

/-- Before `ifma`. -/
def F0 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : IfPub) (t : State) : Prop :=
  HdPre ⟨p.B, p.Z, p.w, p.op, p.oq, l.W, 2 * l.D + 8⟩ t ∧
    WP isa (.block (([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ wsEndT ++
    ([.mov .rdx (.mem (hdr sWsP)), .store (ws .rdx sIfma) .rax, .mov .rdx (.mem (hdr sWsQ)),
      .store (ws .rdx sIfma) .rax, enterP] : List Instr))) t (F1 l p)

theorem regPre_of {p sp sl : Nat} {B : Addr} {Z o a w : Nat} {ep : Addr} {s : State} {mx : BitVec 64} {X : Nat}
    {eb : List Byte} (hoa : o + slot l.W 8 + tabBytes l.W ≤ a) (haZ : a + 2 * l.D + 8 ≤ Z) (hp : p < 2)
    (hsp : sp < 32) (hsl : sl < 32) (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ l.E) (hc : SubCtx s B Z o w l.W mx)
    (hia : word s.mem (off B o) (8 * sIfma) = off B a) (hN : wv s.mem (off B o) (slot l.W Public.aN) l.W = X)
    (hY : wv s.mem (off B o) (slot l.W Public.aY) l.W < X) (hpv : word s.mem B (8 * sp) = ep)
    (hlv : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length) (he : Src s B Z ep eb) :
    RegPre l p sp sl ⟨B, Z, o, a, ep, eb.length⟩ s :=
  ⟨⟨hoa, haZ, hp, hsp, hsl, hL1, hL2⟩, w, mx, X, eb, hc, hia, hN, hY, hpv, hlv, he, rfl⟩

theorem resPre_of {p : Nat} {B : Addr} {Z o a : Nat} {s : State} {mx : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B o) (hH : Hdr s.mem (off B o) l.W mx) (hia : word s.mem (off B o) (8 * sIfma) = off B a)
    (hoa : o + slot l.W 8 + tabBytes l.W ≤ a) (haZ : a + 2 * l.D + 8 ≤ Z) (hp : p < 2)
    (hL : ∀ j < l.L, limb l s.mem (off B a) (l.D * p + l.oY) j < 2 ^ 52)
    (hV : val52 l s.mem (off B a) (l.D * p + l.oY) < 2 * wv s.mem (off B o) (slot l.W Public.aN) l.W) :
    ResPre l p ⟨B, Z, o, a⟩ s :=
  ⟨mx, hs, hdi, hH, hia, hoa, haZ, hp, hL, hV⟩

/-- `ifma_ok`'s hypotheses give `F0`, as `ifma_ok` runs the pieces. -/
theorem ifma_chain (hl : LayOk l) {p : IfPub} {s : State} (h : IfPre l p s) : F0 l p s := by
  obtain ⟨B, Z, w, op, oq, a, ep, eq, lp, lq⟩ := p
  dsimp only [IfPre] at h
  obtain ⟨minv, mp, mq, mk, P, Q, ebp, ebq, hs, hdi, h, hlo, hpq, ha, haZ, hPo, hQo, hYp, hYq, hXp, hXq, hep,
    heq, hLp1, hLp2, hLq1, hLq2, rfl, rfl⟩ := h
  have hn := hs.nowrap
  have hT : tabBytes l.W = 128 * (l.W + 2) := by unfold tabBytes; omega
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have h16 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  have lY := slot_le (w := l.W) (show Public.aY < 8 by decide)
  have lC := slot_le (w := l.W) (show aXc < 8 by decide)
  have hY0 := hdr_lt_slot l.W Public.aY (show 31 < 32 by decide)
  have hC0 := hdr_lt_slot l.W aXc (show 31 < 32 by decide)
  subst ha
  -- The head.
  refine ⟨⟨minv, mq, ⟨hs, hdi, h.nh⟩, hlo, hpq, by simp only; omega, h.wsP, h.wsQ, h.qws⟩, WP.mono
    (headI_ok hl hs hdi h hlo hpq rfl haZ) fun u₁ ⟨m₁, f₁, d₁, k₁⟩ => ?_⟩
  have hf₁ : ∀ {d n}, d + n ≤ op + 8 * sIfma ∨ (op + 8 * sIfma + 8 ≤ d ∧ d + n ≤ oq + 8 * sIfma) ∨
      oq + 8 * sIfma + 8 ≤ d → ∀ r ∈ [(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)], d + n ≤ r.1 ∨ r.1 + r.2 ≤ d :=
    fun hd r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega
  have hYp₁ : wv u₁.mem (off B op) (slot l.W Public.aY) l.W = wv s.mem (off B op) (slot l.W Public.aY) l.W := by
    rw [wv_off, wv_off]; exact f₁.wv_eq (hf₁ (.inr (.inl ⟨by unfold sIfma sFn; omega, by omega⟩))) (by omega)
  have hCp₁ : wv u₁.mem (off B op) (slot l.W aXc) l.W = wv s.mem (off B op) (slot l.W aXc) l.W := by
    rw [wv_off, wv_off]; exact f₁.wv_eq (hf₁ (.inr (.inl ⟨by unfold sIfma sFn; omega, by omega⟩))) (by omega)
  have hZ₁ : ∀ r ∈ [(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)], r.1 + r.2 ≤ Z := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [sIfma, sFn] <;> omega
  have hc₁ := SubCtx.mk' (hs.congr k₁.2.2) m₁.nh m₁.pws d₁ hlo (by omega)
  have hep₁ := hep.congr (InScr.of_frm f₁ hZ₁) k₁.2.1 k₁.2.2
  -- `p`'s region.
  dsimp only [F1]
  refine ⟨regPre_of (by omega) haZ (by decide) (by decide) (by decide) hLp1 hLp2 hc₁ m₁.pia m₁.pn
    (by rw [hYp₁]; exact hYp) m₁.dp m₁.pl hep₁, WP.mono (region_ok hl (p := 0) hc₁ m₁.pia (by omega) haZ (by decide)
      m₁.pn (by rw [hYp₁]; exact hYp) (by decide) (by decide) m₁.dp m₁.pl hep₁ hLp1 hLp2)
    fun u₂ ⟨rp, f₂, w₂, d₂, k₂⟩ => ?_⟩
  have f₂' := f₂.widen (regFr_ifmaR hl (oq := oq) (.inl rfl) (by decide))
  have m₂ := m₁.of_frm hl f₂' hlo hpq (by omega) (by omega)
  have F₂ : Frm B ([(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)] ++ ifmaR l op oq (oq + slot l.W 8 + tabBytes l.W))
      s.mem u₂.mem :=
    (f₁.mono fun r hr => List.mem_append_left _ hr).trans (f₂'.mono fun r hr => List.mem_append_right _ hr)
  have hZF : ∀ r ∈ [(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)] ++ ifmaR l op oq (oq + slot l.W 8 + tabBytes l.W),
      r.1 + r.2 ≤ Z := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hZ₁ r hr
    · have := ifmaR_le hpq (by omega) r hr; omega
  have hs₂ := hs.congr (w₂.trans k₁.2.2)
  -- To `q`'s workspace.
  dsimp only [F2]
  refine ⟨swPre_of hs₂ d₂ m₂.pws.link (by omega), WP.mono (swapWs_ok (o' := oq) hs₂ d₂ m₂.pws.link m₂.wsQ (by decide)
    (by omega)) fun u₃ ⟨d₃, me₃, k₃⟩ => ?_⟩
  rw [← me₃] at m₂ F₂
  have hq₃ : ∀ j, j < 8 → j ≠ Public.aAcc → j ≠ Public.aTmp → j ≠ aT →
      wv u₃.mem (off B oq) (slot l.W j) l.W = wv s.mem (off B oq) (slot l.W j) l.W := fun j hj h1 h2 h3 => by
    have := slot_le (w := l.W) hj
    have := hdr_lt_slot l.W j (show 31 < 32 by decide)
    rw [wv_off, wv_off, me₃, f₂.wv_eq (fun r hr => ?_) (by omega),
      f₁.wv_eq (hf₁ (.inr (.inr (by unfold sIfma sFn; omega)))) (by omega)]
    rcases List.mem_append.mp hr with hr | hr
    · exact .inr (by have := k1sh_lt op r hr; omega)
    · rw [List.mem_singleton.mp hr]; exact .inl (by simp only; omega)
  have k₁₃ := (k₁.trans k₂).trans k₃
  have hc₃ := SubCtx.mk' (hs.congr k₁₃.2.2) m₂.nh m₂.qws d₃ (by omega) (by omega)
  have heq₃ := heq.congr (InScr.of_frm F₂ hZF) k₁₃.2.1 k₁₃.2.2
  have hYq₃ : wv u₃.mem (off B oq) (slot l.W Public.aY) l.W < Q := by
    rw [hq₃ _ (by decide) (by decide) (by decide) (by decide)]; exact hYq
  -- `q`'s region.
  dsimp only [F3]
  refine ⟨regPre_of (by omega) haZ (by decide) (by decide) (by decide) hLq1 hLq2 hc₃ m₂.qia m₂.qn hYq₃ m₂.dq m₂.ql
    heq₃, WP.mono (region_ok hl (p := 1) hc₃ m₂.qia (by omega) haZ (by decide) m₂.qn hYq₃ (by decide) (by decide) m₂.dq
      m₂.ql heq₃ hLq1 hLq2) fun t ⟨rq, f₄, w₄, d₄, k₄⟩ => ?_⟩
  have f₄' := f₄.widen (regFr_ifmaR hl (op := op) (.inr rfl) (by decide))
  rw [ite_eq_left_of_eq_true _ _ (eq_true (rfl : (0 : Nat) = 0)), hYp₁, hCp₁, ← me₃] at rp
  simp only [Nat.one_ne_zero, ↓reduceIte] at rq
  rw [hq₃ _ (by decide) (by decide) (by decide) (by decide),
    hq₃ _ (by decide) (by decide) (by decide) (by decide)] at rq
  have mu := m₂.of_frm hl f₄' hlo hpq (by omega) (by omega)
  have rp' := rp.of_frm hl f₄ (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact .inr (by have := k1sh_lt oq r hr; omega)
    · rw [List.mem_singleton.mp hr]; exact .inl (by simp only; omega)) (by omega)
  have hsu : Scr t B Z := hs.congr (w₄.trans k₁₃.2.2)
  -- The vector code.
  dsimp only [F4]
  refine ⟨vPre_of hsu d₄ mu.qia (by omega), WP.mono (vecI_ok hl (K := False) (C := 0) (wp := l.W) hsu d₄ mu haZ
    (by omega) rp' rq rfl hPo hQo hYp hYq hXp hXq (fun h => h.elim) (fun h => h.elim) (fun h => h.elim)
    (fun h => h.elim) hLp2 hLq2) fun v ⟨⟨gp, _⟩, ⟨gq, _⟩, ov, dv, rdv, wrv, _, kv⟩ => ?_⟩
  have fv : Frm B (ifmaR l op oq (oq + slot l.W 8 + tabBytes l.W)) t.mem v.mem :=
    (Frm.of_outside_off ov (by omega) (by omega)).widen fun r hr =>
      ⟨(oq + slot l.W 8 + tabBytes l.W, 2 * l.D + 8), List.mem_append_right _ (List.mem_singleton_self _),
        by rw [List.mem_singleton.mp hr]; simp only; omega⟩
  have mv := mu.of_frm hl fv hlo hpq (by omega) (by omega)
  have hsv : Scr v B Z := hsu.congr wrv
  have hdv : v.gpr .rdi = off B oq := dv.trans d₄
  -- `q`'s result.
  dsimp only [F5]
  refine ⟨resPre_of hsv hdv mv.qws.hdr mv.qia (by omega) haZ (by decide) gq.lt (by rw [mv.qn]; exact gq.v),
    WP.mono (result_ok hl (p := 1) hsv hdv mv.qws.hdr mv.qia (by omega) haZ (by decide) mv.qn gq.lt gq.v)
    fun t₁ ⟨_, f₁', d₁', k₁'⟩ => ?_⟩
  have m₁' := mv.of_frm hl (f₁'.mono (resSh_ifmaR op oq _ (.inr rfl))) hlo hpq (by omega) (by omega)
  have hs₁ := hsv.congr k₁'.2.2
  have hd₁ : t₁.gpr .rdi = off B oq := d₁'.trans hdv
  -- To `p`'s workspace.
  dsimp only [F6]
  refine ⟨swPre_of hs₁ hd₁ m₁'.qws.link (by omega), WP.mono (swapWs_ok (o' := op) hs₁ hd₁ m₁'.qws.link m₁'.wsP
    (by decide) (by omega)) fun t₂ ⟨d₂', me₂', k₂'⟩ => ?_⟩
  rw [← me₂'] at m₁'
  have gp₂ := goodY_below hl gp (show Frm B _ v.mem t₂.mem by rw [me₂']; exact f₁')
    (fun r hr => by have := resSh_lt oq r hr; omega) (by decide) (by omega)
  have hs₂' := hs₁.congr k₂'.2.2
  -- `p`'s result.
  dsimp only [F7]
  exact ⟨resPre_of hs₂' d₂' m₁'.pws.hdr m₁'.pia (by omega) haZ (by decide) gp₂.1.lt
      (by rw [m₁'.pn]; exact gp₂.1.v),
    WP.mono (result_ok hl (p := 0) hs₂' d₂' m₁'.pws.hdr m₁'.pia (by omega) haZ (by decide) m₁'.pn gp₂.1.lt gp₂.1.v)
      fun t₃ ⟨_, _, d₃', _⟩ => d₃'.trans d₂'⟩

/-- `ifma` is constant time. -/
theorem ifma_ct (hl : LayOk l) : RelCT isa (Two (IfPre l)) (seqs (ifma l)) fun _ _ => True := by
  have hI := ifT hl
  refine two_map id (fun _ _ h => ifma_chain hl h) ?_
  rw [ifma_eq]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine ct_cons (by simp [region]) (two_map (fun p : IfPub => (⟨p.B, p.Z, p.w, p.op, p.oq, l.W, 2 * l.D + 8⟩ : HdPub))
    (fun _ _ h => h.1) head_ct) (fun _ _ h => h.2) ?_
  refine ct_steps (by simp [region, k1, copyArr]) (by simp)
    (fun p : IfPub => (⟨p.B, p.Z, p.op, p.a, p.ep, p.lp⟩ : RegPub)) (fun _ _ h => h.1) (fun _ _ h => h.2)
    (region0_ct hl (by taint_decide)) ?_
  refine ct_cons (by simp [region]) (two_map (fun p : IfPub => (p.B, p.op, p.Z)) (fun _ _ h => h.1)
    (swap_ct sWsQ (by taint_decide))) (fun _ _ h => h.2) ?_
  refine ct_steps (by simp [region, k1, copyArr]) (by simp)
    (fun p : IfPub => (⟨p.B, p.Z, p.oq, p.a, p.eq, p.lq⟩ : RegPub)) (fun _ _ h => h.1) (fun _ _ h => h.2)
    (region1_ct hl (by taint_decide)) ?_
  refine ct_steps (c := [.block [.mov .rbx (.mem (hdr sIfma))], vec l]) (by simp) (by simp [result])
    (fun p : IfPub => (p.B, p.Z, p.oq, p.a)) (fun _ _ h => h.1) (fun _ _ h => h.2) (vecB_ct hI.vec) ?_
  refine ct_steps (by simp [result]) (by simp) (fun p : IfPub => (⟨p.B, p.Z, p.oq, p.a⟩ : ResPub))
    (fun _ _ h => h.1) (fun _ _ h => h.2) (result_ct hl 1 hI.r1 hI.mid) ?_
  refine ct_cons (by simp [result]) (two_map (fun p : IfPub => (p.B, p.oq, p.Z)) (fun _ _ h => h.1)
    (swap_ct sWsP (by taint_decide))) (fun _ _ h => h.2) ?_
  exact ct_steps (by simp [result]) (by simp) (fun p : IfPub => (⟨p.B, p.Z, p.op, p.a⟩ : ResPub))
    (fun _ _ h => h.1) (fun _ _ h => h.2) (result_ct hl 0 hI.r0 hI.mid)
    (two_taint [.rdi] (pins_eqs (fun p _ => off p.B p.op) fun p s (h : F8 p s) r hr => by
      rw [List.mem_singleton.mp hr]; exact h) (by taint_decide))

end VG.Proof.Bignum.X86_64.Ifma
