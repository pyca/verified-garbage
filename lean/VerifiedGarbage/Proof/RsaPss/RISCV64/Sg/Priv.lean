module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Sg.Spec
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivPre
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCall
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivPreCopy
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivPCT
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivVerified
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers

/-!
# RSASSA-PSS signing on RISC-V: the private operation

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Sg/PrivArgs.lean`, `Sg/PrivCall.lean`), with the
frame and the call of RSAES-OAEP decryption (`Proof/RsaOaep/RISCV64/Dc/Priv.lean`).
In the frame of `privBytes` bytes below ours (`pb`), `privArgs` writes
`vg_rsa_private_checked`'s twelve stack arguments at its stack pointer
(`psa`: `p` and `p_len`, saved at `oP`, our stack arguments 0 to 7, the rest
of `scratch` and its length in words) and sets its registers, `n`, `e` and
`e_len` from `oP` (`AtPriv`); the call is narrowed to `n`, `e`, `EM`, the
private key and its stack arguments (`callRd`), and `out` and the rest of
`scratch` (`callWr`), where its precondition holds (`preP_at`); `priv_ok`:
it leaves the signature of `EM` (or zeros) in `out` and its result in `a0`
(`AfterS`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64.Sg

open VG VG.RISCV64
open VG.Impl.RsaOaep.RISCV64 (frameBytes oRsa oEm saved)
open VG.Impl.RsaPss.RISCV64.Sign (privBytes privArgs privArgsM privTail copyArg privCall priv oP)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off off_off fx kR fb fr Saves stackArgAddr_eq sc_in sc_inW)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_ld wp_sd wp_mov wp_li wp_add wp_addi wp_subi wp_sll
  wp_addSp wp_nil)

/-! ## Addresses in the stack the function uses -/

/-- The base of the stack the function uses. -/
abbrev kb (pc : Bool) (s : State) : Addr := s.sp - BitVec.ofNat 64 (stackBytes pc)

/-- The base of the private operation's frame. -/
abbrev pb (pc : Bool) (s : State) : Addr := fb s - BitVec.ofNat 64 (privBytes pc)

/-- The private operation's frame. -/
abbrev PB (pc : Bool) (s : State) : Region := ⟨pb pc s, privBytes pc⟩

/-- Its stack argument `i`, as `privArgs` writes it (12 and 13, `pre` and
`pre_len`, only with `pc`). -/
def psa (s : State) : Nat → BitVec 64
  | 0 => s.gpr .a6
  | 1 => s.gpr .a7
  | 10 => Ss s + BitVec.ofNat 64 oRsa
  | 11 => BitVec.ofNat 64 ((stackArg s 13).toNat - 1024)
  | 12 => stackArg s 16
  | 13 => stackArg s 17
  | i + 2 => stackArg s i

/-- `EM`, and the private operation's part of `scratch`. -/
abbrev emR (s : State) : Region := ⟨off (Ss s) 0, kk s⟩
abbrev rsR (s : State) : Region := ⟨Ss s + BitVec.ofNat 64 oRsa, ((stackArg s 13).toNat - 1024) * 8⟩

/-- The private operation's frame, below its stack arguments. -/
abbrev pkR (pc : Bool) (s : State) : Region := ⟨kb pc s, Impl.Rsa.RISCV64.Priv.frameBytes⟩

section
variable {pc : Bool} {D : Nat} {s : State} (P : PreS pc D s)
include P

theorem kb_add {d : Nat} (hd : d ≤ stackBytes pc) :
    kb pc s + BitVec.ofNat 64 d = s.sp - BitVec.ofNat 64 (stackBytes pc - d) := by
  have := P.sp1; have := stackBytes_ge pc
  apply BitVec.eq_of_toNat_eq
  simp only [kb, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] at *
  omega

omit P in
theorem privBytes_rng (pc : Bool) : 96 ≤ privBytes pc ∧ privBytes pc ≤ 112 := by cases pc <;> decide

omit P in
theorem stackBytes_split (pc : Bool) :
    stackBytes pc = frameBytes + privBytes pc + Impl.Rsa.RISCV64.Priv.frameBytes := rfl

theorem fb_kb : fb s = kb pc s + BitVec.ofNat 64 (privBytes pc + Impl.Rsa.RISCV64.Priv.frameBytes) := by
  rw [kb_add P (by rw [stackBytes_split]; omega)]
  have e : stackBytes pc - (privBytes pc + Impl.Rsa.RISCV64.Priv.frameBytes) = frameBytes := by
    rw [stackBytes_split]; omega
  rw [e]

theorem pb_kb : pb pc s = kb pc s + BitVec.ofNat 64 3248 := by
  rw [kb_add P (by rw [stackBytes_split]; unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega)]
  have := P.sp1; have := privBytes_rng pc
  rw [stackBytes_split] at *
  apply BitVec.eq_of_toNat_eq
  simp only [pb, fb, BitVec.toNat_sub, BitVec.toNat_ofNat, frameBytes, Impl.Rsa.RISCV64.Priv.frameBytes] at *
  omega

theorem kb_toNat : (kb pc s).toNat = s.sp.toNat - stackBytes pc := by
  have := P.sp1; have := stackBytes_ge pc
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat] at *
  omega

omit P in
theorem kb_sub {d n : Nat} (h : d + n ≤ stackBytes pc) : Region.Sub ⟨kb pc s + BitVec.ofNat 64 d, n⟩ (kS pc s) :=
  Offset.sub_base _ h

theorem pb_al : (pb pc s).toNat % 16 = 0 := by
  have := P.sp1; have := P.spal; have := privBytes_rng pc
  have h16 : privBytes pc % 16 = 0 := by cases pc <;> decide
  rw [stackBytes_split] at *
  simp only [pb, fb, BitVec.toNat_sub, BitVec.toNat_ofNat, frameBytes, Impl.Rsa.RISCV64.Priv.frameBytes] at *
  omega

theorem pb_off_al {d : Nat} (hd : d % 8 = 0) : (pb pc s + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  have := pb_al P; have := s.sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at *
  omega

theorem pb_sub {d n : Nat} (h : d + n ≤ privBytes pc) :
    Region.Sub ⟨pb pc s + BitVec.ofNat 64 d, n⟩ (kS pc s) := by
  rw [pb_kb P, Offset.add_add]
  exact kb_sub (by rw [stackBytes_split]; unfold frameBytes Impl.Rsa.RISCV64.Priv.frameBytes; omega)

theorem PB_sub : Region.Sub (PB pc s) (kS pc s) := by
  have := pb_sub P (d := 0) (n := privBytes pc) (by omega); rwa [BitVec.add_zero] at this

theorem pb_top : pb pc s + BitVec.ofNat 64 (privBytes pc + frameBytes) = s.sp := by
  have := P.sp1; have := privBytes_rng pc
  rw [stackBytes_split] at *
  apply BitVec.eq_of_toNat_eq
  simp only [pb, fb, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, frameBytes,
    Impl.Rsa.RISCV64.Priv.frameBytes] at *
  omega

theorem sl_sub : stackArg s 13 - BitVec.ofNat 64 1024 = BitVec.ofNat 64 ((stackArg s 13).toNat - 1024) := by
  have := scLen P; unfold oRsa at this
  have := (stackArg s 13).isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- Our frame's slots, apart from the private operation's frame. -/
theorem slots_PB : Region.Disjoint ⟨fb s + BitVec.ofNat 64 Proof.RsaOaep.RISCV64.oSv, frameBytes -
    Proof.RsaOaep.RISCV64.oSv⟩ (PB pc s) := by
  show Region.Disjoint _ ⟨pb pc s, privBytes pc⟩
  have := privBytes_rng pc
  rw [fb_kb P, Offset.add_add, pb_kb P]
  exact Offset.disjoint _ (.inr (by unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega))
    (by unfold frameBytes Impl.Rsa.RISCV64.Priv.frameBytes Proof.RsaOaep.RISCV64.oSv; omega)
    (by omega)

/-- A range of our part of `scratch`, in `scratch`. -/
theorem sc_scR {o n : Nat} (h : o + n ≤ oRsa) : Region.Sub ⟨off (Ss s) o, n⟩ (scR s) :=
  fun a ha => sc_sub P a (sc_in (S := Ss) (s := s) h a ha)

theorem em_sub : Region.Sub (emR s) (scR s) := sc_scR P (by have : kk s ≤ 1024 := P.k2; unfold oRsa; omega)

theorem rs_sub : Region.Sub (rsR s) (scR s) := by
  have := scLen P
  exact Offset.sub_base _ (by unfold oRsa at *; omega)

omit P in
theorem pk_sub : Region.Sub (pkR pc s) (kS pc s) := by
  have := Offset.sub_base (kb pc s) (d := 0) (n := Impl.Rsa.RISCV64.Priv.frameBytes) (k := stackBytes pc)
    (by have := stackBytes_ge pc; unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega)
  rwa [BitVec.add_zero] at this

theorem em_rs : (emR s).Disjoint (rsR s) := by
  have := P.wsc; have : kk s ≤ 1024 := P.k2; have := scLen P
  have e : emR s = ⟨Ss s, kk s⟩ := by simp only [emR, off, BitVec.add_zero]
  rw [e]
  exact Offset.base_disjoint _ (by unfold oRsa at *; omega) (by unfold oRsa at *; omega)

theorem pk_PB : (pkR pc s).Disjoint (PB pc s) := by
  show Region.Disjoint _ ⟨pb pc s, privBytes pc⟩
  have := privBytes_rng pc
  rw [pb_kb P]
  exact Offset.base_disjoint _ (by decide)
    (by omega)

/-- The saved arguments, kept by writes to the private operation's frame. -/
theorem Spilled.pb {m m' : Mem} (sp : Spilled s m) (hf : Frame [PB pc s] m m') : Spilled s m' := by
  have e : ∀ j < 6, m'.readW (off (Ss s) (oP + 8 * j)) 64 = m.readW (off (Ss s) (oP + 8 * j)) 64 := fun j hj =>
    hf.readW (r := ⟨off (Ss s) (oP + 8 * j), 8⟩) (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ((P.ks.sub_left (PB_sub P)).sub_right (sc_scR P (by unfold oP oRsa; omega))).symm) (by decide)
  exact ⟨(e 0 (by decide)).trans sp.n, (e 1 (by decide)).trans sp.e, (e 2 (by decide)).trans sp.el,
    (e 3 (by decide)).trans sp.p, (e 4 (by decide)).trans sp.pl, (e 5 (by decide)).trans sp.c⟩

/-- A load of our stack argument `j` through `t6`, with memory changed only
in the stack the function uses and our part of `scratch`. -/
theorem wp_argS {t : State} {r : Reg} {j : Nat} {is : List Instr} {Q : State → Prop} (hj : j < 16)
    (h6 : t.gpr .t6 = s.sp) (hrd : t.rd = s.rd) (hm : Frame [kS pc s, SC Ss s] s.mem t.mem)
    (k : ∀ t', Only [r] t t' → t'.gpr r = stackArg s j → WP isa (.block is) t' Q)
    (ho : 8 * j < 2048 := by decide) :
    WP isa (.block (.load .d r .t6 (8 * j) :: is)) t Q := by
  refine wp_ld (a := stackArgAddr s j) (by rw [h6]; rfl) (arg_al P hj) ?_ (fun t' o e => k t' o ?_) ho
  · rw [hrd, P.hrd]; exact ⟨aR pc s, by cases pc <;> simp, in_aR hj⟩
  · rw [e, stackArg, hm.readW (in_aR hj) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact P.ka.symm
      · exact (P.sa.sub_left (sc_sub P)).symm) (by decide)]

end

/-! ## The arguments -/

/-- In the private operation's frame, after `privArgsM`, with `EM` holding
`em`. -/
structure AtPrivM (pc : Bool) (s : State) (em : List Byte) (t : State) : Prop where
  sp : t.sp = pb pc s
  rd : t.rd = s.rd
  wr : t.wr = PB pc s :: fr s :: s.wr
  mem : Frame [kS pc s, SC Ss s] s.mem t.mem
  em : Spec.Rsa.bytesAt t.mem (off (Ss s) 0) (kk s) = em
  sv : Spill.Saved (fb s) s.gpr saved t.mem
  a0 : t.gpr .a0 = s.gpr .a0
  a1 : t.gpr .a1 = s.gpr .a3
  a2 : t.gpr .a2 = s.gpr .a2
  a3 : t.gpr .a3 = s.gpr .a3
  a4 : t.gpr .a4 = s.gpr .a4
  a5 : t.gpr .a5 = s.gpr .a5
  a6 : t.gpr .a6 = off (Ss s) 0
  a7 : t.gpr .a7 = s.gpr .a3
  psa : ∀ i < 12, t.mem.readW (pb pc s + BitVec.ofNat 64 (8 * i)) 64 = psa s i
  t6 : t.gpr .t6 = s.sp
  t0 : t.gpr .t0 = pb pc s

/-- At the call: with `pc`, `pre` and `pre_len` in its stack arguments 12 and
13 too. -/
structure AtPriv (pc : Bool) (s : State) (em : List Byte) (t : State) : Prop extends AtPrivM pc s em t where
  psx : pc = true → ∀ i, 12 ≤ i → i < 14 →
    t.mem.readW (pb pc s + BitVec.ofNat 64 (8 * i)) 64 = VG.Proof.RsaPss.RISCV64.Sg.psa s i

/-- After the first `n` copies of our stack arguments, from `w`. -/
structure Cp (pc : Bool) (s w : State) (n : Nat) (t : State) : Prop where
  keep : Kept [.t1] w t
  mem : Frame [PB pc s] w.mem t.mem
  z0 : t.mem.readW (pb pc s + BitVec.ofNat 64 0) 64 = w.mem.readW (pb pc s + BitVec.ofNat 64 0) 64
  z1 : t.mem.readW (pb pc s + BitVec.ofNat 64 8) 64 = w.mem.readW (pb pc s + BitVec.ofNat 64 8) 64
  got : ∀ j < n, t.mem.readW (pb pc s + BitVec.ofNat 64 (8 * (j + 2))) 64 = stackArg s j

section
variable {pc : Bool} {D : Nat} {s : State} (P : PreS pc D s)
include P

omit P in theorem pb_in {d : Nat} (h : d + 8 ≤ privBytes pc) {rs : List Region} :
    InRegions (PB pc s :: rs) (pb pc s + BitVec.ofNat 64 d) 8 :=
  ⟨_, List.mem_cons_self .., Offset.contains_base _ h (by have := privBytes_rng pc; omega)⟩

theorem copy_step {w : State} (hw0 : w.gpr .t0 = pb pc s) (hw6 : w.gpr .t6 = s.sp) (hrd : w.rd = s.rd)
    (hwr : w.wr = PB pc s :: fr s :: s.wr) (hm : Frame [kS pc s, SC Ss s] s.mem w.mem) {n : Nat} (hn : n < 8)
    {t : State} (hc : Cp pc s w n t) : WP isa (.block (copyArg n)) t (Cp pc s w (n + 1)) := by
  have hmt : Frame [kS pc s, SC Ss s] s.mem t.mem := hm.trans (hc.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., PB_sub P⟩)
  unfold copyArg
  refine wp_argS P (j := n) (by omega) (by rw [hc.keep.get .t6, hw6]) (hc.keep.rd.trans hrd) hmt
    (fun t₁ o₁ e₁ => ?_) (by omega)
  refine wp_sd (a := pb pc s + BitVec.ofNat 64 (8 * (n + 2))) (by rw [o₁.get .t0, hc.keep.get .t0, hw0])
    (pb_off_al P (by omega))
    (by rw [o₁.wr, hc.keep.wr, hwr]; exact pb_in (by have := privBytes_rng pc; omega)) (fun t₂ m₂ => wp_nil ?_)
    (by omega)
  rw [e₁] at m₂
  refine ⟨(hc.keep.trans (o₁.keep.trans m₂.keep)).mono, ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [m₂.mem, o₁.mem]
    exact hc.mem.writeW (List.mem_singleton_self _) _ (Offset.contains_base (pb pc s) (d := 8 * (n + 2)) (n := 8)
      (k := privBytes pc) (by have := privBytes_rng pc; omega) (by omega))
  · rw [m₂.mem, o₁.mem, Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
    exact hc.z0
  · rw [m₂.mem, o₁.mem, Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
    exact hc.z1
  · rw [m₂.mem, o₁.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
      exact hc.got j hj
    · rw [Mem.readW_writeW_self64]

theorem copies_ok {w : State} (hw0 : w.gpr .t0 = pb pc s) (hw6 : w.gpr .t6 = s.sp) (hrd : w.rd = s.rd)
    (hwr : w.wr = PB pc s :: fr s :: s.wr) (hm : Frame [kS pc s, SC Ss s] s.mem w.mem) :
    WP isa (.block ((List.range 8).flatMap copyArg)) w (Cp pc s w 8) :=
  wp_range_flatMap (M := isa) (Cp pc s w) (fun _ _ hn hc => copy_step P hw0 hw6 hrd hwr hm hn hc) 8
    (Nat.le_refl _) w ⟨Kept.refl _ _, Frame.refl _ _, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- A load of the saved argument `j`. -/
theorem wp_ldP {u : State} (hs0 : u.gpr .s0 = Ss s) (hwr : u.wr = PB pc s :: fr s :: s.wr) {r : Reg} {j : Nat}
    (hj : j < 5) {is : List Instr} {Q : State → Prop}
    (k : ∀ u', Only [r] u u' → u'.gpr r = u.mem.readW (off (Ss s) (oP + 8 * j)) 64 → WP isa (.block is) u' Q)
    (ho : oP + 8 * j < 2048 := by decide) :
    WP isa (.block (.load .d r .s0 (oP + 8 * j) :: is)) u Q := by
  refine wp_ld (a := off (Ss s) (oP + 8 * j)) (by rw [hs0]) (oP_al P j) ?_ k ho
  obtain ⟨r, hr, hc⟩ := sc_inW (fits P) (o := oP + 8 * j) (n := 8) (by unfold oP oRsa; omega)
  exact ⟨r, List.mem_append_right _ (by rw [hwr]; exact List.mem_cons_of_mem _ hr), hc⟩

theorem privArgsM_ok {t : State} (h : Base Ss vS s t) (sp : Spilled s t.mem) {em : List Byte}
    (hem : Spec.Rsa.bytesAt t.mem (off (Ss s) 0) (kk s) = em) :
    WP isa (.block (privArgsM pc)) (allocd (privBytes pc) t) (AtPrivM pc s em) := by
  have hsp : t.sp = fb s := h.sp
  have usp : (allocd (privBytes pc) t).sp = pb pc s := by show t.sp - _ = _; rw [hsp]
  have uwr : (allocd (privBytes pc) t).wr = PB pc s :: fr s :: s.wr := by
    show (⟨t.sp - _, _⟩ : Region) :: t.wr = _; rw [hsp, h.wr]
  have urd : (allocd (privBytes pc) t).rd = s.rd := h.rd
  have hmS : Frame [kS pc s, SC Ss s] s.mem t.mem := h.mem.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨kS pc s, List.mem_cons_self .., kR_sub⟩
    · exact ⟨SC Ss s, by simp, fun _ h => h⟩
  have inPB : ∀ {d : Nat}, d + 8 ≤ privBytes pc → (PB pc s).Contains (pb pc s + BitVec.ofNat 64 d) 8 :=
    fun {d} hd => Offset.contains_base _ hd (by have := privBytes_rng pc; omega)
  have toS : ∀ {m : Mem}, Frame [PB pc s] t.mem m → Frame [kS pc s, SC Ss s] s.mem m := fun hf =>
    hmS.trans (hf.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., PB_sub P⟩)
  unfold privArgsM
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp (imm := 0) (fun w₁ o₁ e₁ => wp_addSp (imm := privBytes pc + frameBytes) (fun w₂ o₂ e₂ => ?_)
    (by cases pc <;> decide)) (by decide)
  rw [usp] at e₁
  have O₂ : Only [.t0, .t6] (allocd (privBytes pc) t) w₂ := o₁.trans o₂
  have g0 : w₂.gpr .t0 = pb pc s := by rw [o₂.get .t0, e₁, BitVec.add_zero]
  have g6 : w₂.gpr .t6 = s.sp := by rw [e₂, o₁.sp, usp, pb_top P]
  have gs0 : w₂.gpr .s0 = Ss s := by rw [O₂.get .s0]; exact h.s0
  have wr₂ : w₂.wr = PB pc s :: fr s :: s.wr := O₂.wr.trans uwr
  -- `p` and `p_len`.
  refine wp_ldP P (j := 3) gs0 wr₂ (by decide) fun w₃ o₃ e₃ => ?_
  have v₃ : w₃.gpr .t1 = s.gpr .a6 := by rw [e₃, O₂.mem]; exact sp.p
  refine wp_sd (a := pb pc s + BitVec.ofNat 64 0) (by rw [o₃.get .t0, g0]) (pb_off_al P (by decide))
    (by rw [o₃.wr, wr₂]; exact pb_in (by have := privBytes_rng pc; omega)) (fun w₄ m₄ => ?_) (by decide)
  have f₄ : Frame [PB pc s] t.mem w₄.mem := by
    rw [m₄.mem, o₃.mem, O₂.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (inPB (by have := privBytes_rng pc; omega))
  refine wp_ldP P (j := 4) (by rw [m₄.gpr, o₃.get .s0, gs0]) (m₄.wr.trans (o₃.wr.trans wr₂)) (by decide)
    fun w₅ o₅ e₅ => ?_
  have v₅ : w₅.gpr .t1 = s.gpr .a7 := by rw [e₅]; exact (sp.pb P f₄).pl
  refine wp_sd (a := pb pc s + BitVec.ofNat 64 8) (by rw [o₅.get .t0, m₄.gpr, o₃.get .t0, g0])
    (pb_off_al P (by decide)) (by rw [o₅.wr, m₄.wr, o₃.wr, wr₂]; exact pb_in (by have := privBytes_rng pc; omega)) (fun w₆ m₆ => ?_)
    (by decide)
  have K₆ : Kept [.t1] w₂ w₆ := (o₃.keep.trans (m₄.keep.trans (o₅.keep.trans m₆.keep))).mono
  have f₆ : Frame [PB pc s] t.mem w₆.mem := by
    rw [m₆.mem, o₅.mem]; exact f₄.writeW (List.mem_singleton_self _) _ (inPB (by have := privBytes_rng pc; omega))
  have hw0 : w₆.gpr .t0 = pb pc s := by rw [K₆.get .t0, g0]
  have hw6 : w₆.gpr .t6 = s.sp := by rw [K₆.get .t6, g6]
  have hrd : w₆.rd = s.rd := K₆.rd.trans (O₂.rd.trans urd)
  have hwr : w₆.wr = PB pc s :: fr s :: s.wr := K₆.wr.trans wr₂
  have z0 : w₆.mem.readW (pb pc s + BitVec.ofNat 64 0) 64 = psa s 0 := by
    rw [m₆.mem, o₅.mem, Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide),
      m₄.mem, Mem.readW_writeW_self64]; exact v₃
  have z1 : w₆.mem.readW (pb pc s + BitVec.ofNat 64 8) 64 = psa s 1 := by
    rw [m₆.mem, Mem.readW_writeW_self64]; exact v₅
  -- Our stack arguments 0 to 7.
  rw [WP.block_append_iff]
  refine WP.mono (copies_ok P hw0 hw6 hrd hwr (toS f₆)) fun v hc => ?_
  have v0 : v.gpr .t0 = pb pc s := by rw [hc.keep.get .t0, hw0]
  have v6 : v.gpr .t6 = s.sp := by rw [hc.keep.get .t6, hw6]
  have vrd : v.rd = s.rd := hc.keep.rd.trans hrd
  have vwr : v.wr = PB pc s :: fr s :: s.wr := hc.keep.wr.trans hwr
  have fv : Frame [PB pc s] t.mem v.mem := f₆.trans hc.mem
  have Kv : Kept [.t1, .t0, .t6] (allocd (privBytes pc) t) v := (O₂.keep.trans (K₆.trans hc.keep)).mono
  have gv : ∀ r ∈ [Reg.s0, .s1, .s2, .s3, .s4], v.gpr r = t.gpr r := fun r hr => by
    rw [Kv.gpr r (by revert r; decide)]; rfl
  -- The rest of `scratch` and its length.
  refine wp_li (imm := 1024) (by decide) fun x₁ o₁ e₁ => wp_sll (sh := 3) (fun x₂ o₂ e₂ =>
    wp_add fun x₃ o₃ e₃ => ?_) (by decide)
  have O₃ : Only [.t1] v x₃ := (o₁.trans (o₂.trans o₃)).mono
  refine wp_sd (a := pb pc s + BitVec.ofNat 64 80) (by rw [O₃.get .t0, v0]) (pb_off_al P (by decide))
    (by rw [O₃.wr, vwr]; exact pb_in (by have := privBytes_rng pc; omega)) (fun x₄ m₄ => ?_) (by decide)
  have f₄' : Frame [PB pc s] t.mem x₄.mem := by
    rw [m₄.mem, O₃.mem]; exact fv.writeW (List.mem_singleton_self _) _ (inPB (by have := privBytes_rng pc; omega))
  refine wp_argS P (j := 13) (by decide) (by rw [m₄.gpr, O₃.get .t6, v6]) (m₄.rd.trans (O₃.rd.trans vrd))
    (toS f₄') (fun x₅ o₅ e₅ => wp_subi (imm := 1024) (fun x₆ o₆ e₆ => ?_) (by decide))
  have K₆' : Kept [.t1] v x₆ := (O₃.keep.trans (m₄.keep.trans (o₅.keep.trans o₆.keep))).mono
  refine wp_sd (a := pb pc s + BitVec.ofNat 64 88) (by rw [K₆'.get .t0, v0]) (pb_off_al P (by decide))
    (by rw [K₆'.wr, vwr]; exact pb_in (by have := privBytes_rng pc; omega)) (fun x₇ m₇ => ?_) (by decide)
  have K₇ : Kept [.t1] v x₇ := (K₆'.trans m₇.keep).mono
  have f₇ : Frame [PB pc s] t.mem x₇.mem := by
    rw [m₇.mem, (o₅.trans o₆).mem]; exact f₄'.writeW (List.mem_singleton_self _) _ (inPB (by have := privBytes_rng pc; omega))
  have sp₇ : Spilled s x₇.mem := sp.pb P f₇
  have x0 : x₇.gpr .s0 = Ss s := by rw [K₇.get .s0, gv .s0 (by decide)]; exact h.s0
  have x1 : x₇.gpr .s1 = s.gpr .a3 := by rw [K₇.get .s1, gv .s1 (by decide)]; exact Base.sk h
  have x2 : x₇.gpr .s2 = s.gpr .a0 := by rw [K₇.get .s2, gv .s2 (by decide)]; exact Base.sout h
  have xwr : x₇.wr = PB pc s :: fr s :: s.wr := K₇.wr.trans vwr
  -- The registers.
  refine wp_mov fun x₈ o₈ e₈ => wp_mov fun x₉ o₉ e₉ => ?_
  have O₉ : Only [.a0, .a1] x₇ x₉ := (o₈.trans o₉).mono
  refine wp_ldP P (j := 0) (by rw [O₉.get .s0, x0]) (O₉.wr.trans xwr) (by decide) fun x₁₀ o₁₀ e₁₀ => ?_
  refine wp_mov fun x₁₁ o₁₁ e₁₁ => ?_
  have O₁₁ : Only [.a0, .a1, .a2, .a3] x₇ x₁₁ := (O₉.trans (o₁₀.trans o₁₁)).mono
  refine wp_ldP P (j := 1) (by rw [O₁₁.get .s0, x0]) (O₁₁.wr.trans xwr) (by decide) fun x₁₂ o₁₂ e₁₂ => ?_
  have O₁₂ : Only [.a0, .a1, .a2, .a3, .a4] x₇ x₁₂ := (O₁₁.trans o₁₂).mono
  refine wp_ldP P (j := 2) (by rw [O₁₂.get .s0, x0]) (O₁₂.wr.trans xwr) (by decide) fun x₁₃ o₁₃ e₁₃ => ?_
  refine wp_addi (imm := oEm) (fun x₁₄ o₁₄ e₁₄ => wp_mov fun x₁₅ o₁₅ e₁₅ => wp_nil ?_) (by decide)
  have T : Only [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] x₇ x₁₅ := (O₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅))).mono
  have K : Kept [.t1, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] v x₁₅ := (K₇.trans T.keep).mono
  have hpb : Frame [PB pc s] t.mem x₁₅.mem := by rw [T.mem]; exact f₇
  have hfm : x₁₅.mem = (v.mem.writeW (pb pc s + BitVec.ofNat 64 80) (x₃.gpr .t1)).writeW
      (pb pc s + BitVec.ofNat 64 88) (x₆.gpr .t1) := by
    rw [T.mem, m₇.mem, (o₅.trans o₆).mem, m₄.mem, O₃.mem]
  have t80 : x₃.gpr .t1 = psa s 10 := by
    rw [e₃, o₂.get .s0, o₁.get .s0, e₂, e₁, gv .s0 (by decide), h.s0]
    show _ = Ss s + BitVec.ofNat 64 8192
    congr 1
  have t88 : x₆.gpr .t1 = psa s 11 := by rw [e₆, e₅]; exact sl_sub P
  have r2 : ∀ d, d + 8 ≤ 80 → ((v.mem.writeW (pb pc s + BitVec.ofNat 64 80) (x₃.gpr .t1)).writeW
      (pb pc s + BitVec.ofNat 64 88) (x₆.gpr .t1)).readW (pb pc s + BitVec.ofNat 64 d) 64 =
      v.mem.readW (pb pc s + BitVec.ofNat 64 d) 64 := fun d hd => by
    rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
  have hg := hc.got
  have hemR : ∀ r ∈ [PB pc s], Region.Disjoint (emR s) r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ((P.ks.sub_left (PB_sub P)).sub_right (em_sub P)).symm
  refine {
    sp := K.sp.trans (Kv.sp.trans usp)
    rd := K.rd.trans vrd
    wr := K.wr.trans vwr
    mem := toS hpb
    em := by
      rw [← hem]
      simp only [Spec.Rsa.bytesAt]
      exact List.map_congr_left fun i hi => hpb.bytes (R := emR s) hemR
        (by have : kk s ≤ 1024 := P.k2; show kk s ≤ _; omega) (List.mem_range.mp hi)
    sv := h.sv.sv.frame_in (lo := Proof.RsaOaep.RISCV64.oSv) (n := frameBytes - Proof.RsaOaep.RISCV64.oSv)
        (fun p hp => by
          have := Proof.RsaOaep.RISCV64.saved_offs p hp; unfold frameBytes Proof.RsaOaep.RISCV64.oSv at *; omega)
        hpb
      fun r hr => by rw [List.mem_singleton.mp hr]; exact slots_PB P
    a0 := by
      rw [(o₉.trans (o₁₀.trans (o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅)))))).get .a0, e₈, x2]
    a1 := by
      rw [(o₁₀.trans (o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅))))).get .a1, e₉, o₈.get .s1, x1]
    a2 := by
      rw [(o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅)))).get .a2, e₁₀, O₉.mem]; exact sp₇.n
    a3 := by
      rw [(o₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅))).get .a3, e₁₁, (O₉.trans o₁₀).get .s1, x1]
    a4 := by
      rw [(o₁₃.trans (o₁₄.trans o₁₅)).get .a4, e₁₂, O₁₁.mem]; exact sp₇.e
    a5 := by
      rw [(o₁₄.trans o₁₅).get .a5, e₁₃, O₁₂.mem]; exact sp₇.el
    a6 := by
      rw [o₁₅.get .a6, e₁₄, (O₁₂.trans o₁₃).get .s0, x0]; rfl
    a7 := by
      rw [e₁₅, (O₁₂.trans (o₁₃.trans o₁₄)).get .s1, x1]
    psa := fun i hi => by
      rw [hfm]
      match i, hi with
      | 0, _ => exact (r2 _ (by decide)).trans (hc.z0.trans z0)
      | 1, _ => exact (r2 _ (by decide)).trans (hc.z1.trans z1)
      | 2, _ => exact (r2 _ (by decide)).trans (hg 0 (by decide))
      | 3, _ => exact (r2 _ (by decide)).trans (hg 1 (by decide))
      | 4, _ => exact (r2 _ (by decide)).trans (hg 2 (by decide))
      | 5, _ => exact (r2 _ (by decide)).trans (hg 3 (by decide))
      | 6, _ => exact (r2 _ (by decide)).trans (hg 4 (by decide))
      | 7, _ => exact (r2 _ (by decide)).trans (hg 5 (by decide))
      | 8, _ => exact (r2 _ (by decide)).trans (hg 6 (by decide))
      | 9, _ => exact (r2 _ (by decide)).trans (hg 7 (by decide))
      | 10, _ =>
        show Mem.readW _ (pb pc s + BitVec.ofNat 64 80) 64 = _
        rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide),
          Mem.readW_writeW_self64]
        exact t80
      | 11, _ =>
        show Mem.readW _ (pb pc s + BitVec.ofNat 64 88) 64 = _
        rw [Mem.readW_writeW_self64]
        exact t88
    t6 := by rw [K.get .t6, v6]
    t0 := by rw [K.get .t0, v0] }

/-- With `pc`, `privTail` copies `pre` and `pre_len` (our stack arguments 16
and 17) to its stack arguments 12 and 13. -/
theorem privTail_ok {t : State} {em : List Byte} (A : AtPrivM pc s em t) :
    WP isa (.block (privTail pc)) t (AtPriv pc s em) := by
  cases pc with
  | false => exact wp_nil ⟨A, fun h => nomatch h⟩
  | true =>
  have sp3 := (P.px rfl).sp3
  have inA : ∀ {j : Nat} {ws : List Region}, j < 18 → InRegions (s.rd ++ ws) (stackArgAddr s j) 8 :=
    fun hj => by rw [P.hrd]; exact ⟨aR true s, by simp, in_aR18 hj⟩
  have toK : Frame [kS true s, SC Ss s] s.mem t.mem := A.mem
  have ld : ∀ {u : State} {j : Nat}, j < 18 → Frame [kS true s, SC Ss s] s.mem u.mem →
      u.mem.readW (stackArgAddr s j) 64 = stackArg s j := fun {u j} hj hm =>
    hm.readW (in_aR18 hj) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact P.ka.symm
      · exact (P.sa.sub_left (sc_sub P)).symm) (by decide)
  simp only [privTail]
  refine wp_ld (a := stackArgAddr s 16) (by rw [A.t6]; rfl) (arg_al18 P (by decide))
    (by rw [A.rd]; exact inA (j := 16) (by decide)) (fun t₁ o₁ e₁ => ?_) (by decide)
  refine wp_sd (a := pb true s + BitVec.ofNat 64 96) (by rw [o₁.get .t0, A.t0]) (pb_off_al P (by decide))
    (by rw [o₁.wr, A.wr]; exact pb_in (by decide)) (fun t₂ m₂ => ?_) (by decide)
  have f₂ : Frame [PB true s] t.mem t₂.mem := by
    rw [m₂.mem, o₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (d := 96) (by decide) (by decide))
  have hm₂ : Frame [kS true s, SC Ss s] s.mem t₂.mem := toK.trans (f₂.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., PB_sub P⟩)
  refine wp_ld (a := stackArgAddr s 17) (by rw [m₂.gpr, o₁.get .t6, A.t6]; rfl) (arg_al18 P (by decide))
    (by rw [m₂.rd, o₁.rd, A.rd]; exact inA (j := 17) (by decide)) (fun t₃ o₃ e₃ => ?_) (by decide)
  refine wp_sd (a := pb true s + BitVec.ofNat 64 104) (by rw [o₃.get .t0, m₂.gpr, o₁.get .t0, A.t0])
    (pb_off_al P (by decide)) (by rw [o₃.wr, m₂.wr, o₁.wr, A.wr]; exact pb_in (by decide))
    (fun t₄ m₄ => wp_nil ?_) (by decide)
  have K : Kept [.t1] t t₄ := (o₁.keep.trans (m₂.keep.trans (o₃.keep.trans m₄.keep))).mono
  have f₄ : Frame [PB true s] t.mem t₄.mem := by
    rw [m₄.mem, o₃.mem]
    exact f₂.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (d := 104) (by decide) (by decide))
  have hm₄ : Frame [kS true s, SC Ss s] s.mem t₄.mem := toK.trans (f₄.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., PB_sub P⟩)
  have hmem : t₄.mem = (t.mem.writeW (pb true s + BitVec.ofNat 64 96) (t₁.gpr .t1)).writeW
      (pb true s + BitVec.ofNat 64 104) (t₃.gpr .t1) := by
    rw [m₄.mem, o₃.mem, m₂.mem, o₁.mem]
  have r12 : ∀ d, d + 8 ≤ 96 → t₄.mem.readW (pb true s + BitVec.ofNat 64 d) 64 =
      t.mem.readW (pb true s + BitVec.ofNat 64 d) 64 := fun d hd => by
    rw [hmem, Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
  have hemR : ∀ r ∈ [PB true s], Region.Disjoint (emR s) r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ((P.ks.sub_left (PB_sub P)).sub_right (em_sub P)).symm
  refine ⟨{
    sp := K.sp.trans A.sp
    rd := K.rd.trans A.rd
    wr := K.wr.trans A.wr
    mem := hm₄
    em := by
      rw [← A.em]
      simp only [Spec.Rsa.bytesAt]
      exact List.map_congr_left fun i hi => f₄.bytes (R := emR s) hemR
        (by have : kk s ≤ 1024 := P.k2; show kk s ≤ _; omega) (List.mem_range.mp hi)
    sv := A.sv.frame_in (lo := Proof.RsaOaep.RISCV64.oSv) (n := frameBytes - Proof.RsaOaep.RISCV64.oSv)
        (fun p hp => by
          have := Proof.RsaOaep.RISCV64.saved_offs p hp; unfold frameBytes Proof.RsaOaep.RISCV64.oSv at *; omega)
        f₄ fun r hr => by rw [List.mem_singleton.mp hr]; exact slots_PB P
    a0 := by rw [K.get .a0]; exact A.a0
    a1 := by rw [K.get .a1]; exact A.a1
    a2 := by rw [K.get .a2]; exact A.a2
    a3 := by rw [K.get .a3]; exact A.a3
    a4 := by rw [K.get .a4]; exact A.a4
    a5 := by rw [K.get .a5]; exact A.a5
    a6 := by rw [K.get .a6]; exact A.a6
    a7 := by rw [K.get .a7]; exact A.a7
    psa := fun i (hi : i < 12) => (r12 (8 * i) (by omega)).trans (A.psa i hi)
    t6 := by rw [K.get .t6]; exact A.t6
    t0 := by rw [K.get .t0]; exact A.t0 }, fun _ i h1 h2 => ?_⟩
  have e₁' : t₁.gpr .t1 = stackArg s 16 := by rw [e₁]; exact ld (by decide) toK
  have e₃' : t₃.gpr .t1 = stackArg s 17 := by rw [e₃]; exact ld (by decide) hm₂
  match i, h1, h2 with
  | 12, _, _ =>
    show t₄.mem.readW (pb true s + BitVec.ofNat 64 96) 64 = _
    rw [hmem, Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
    exact e₁'
  | 13, _, _ =>
    show t₄.mem.readW (pb true s + BitVec.ofNat 64 104) 64 = _
    rw [hmem, Mem.readW_writeW_self64]
    exact e₃'

theorem privArgs_ok {t : State} (h : Base Ss vS s t) (sp : Spilled s t.mem)
    {em : List Byte} (hem : Spec.Rsa.bytesAt t.mem (off (Ss s) 0) (kk s) = em) :
    WP isa (.block (privArgs pc)) (allocd (privBytes pc) t) (AtPriv pc s em) := by
  unfold privArgs
  rw [WP.block_append_iff]
  exact WP.mono (privArgsM_ok P h sp hem) fun u A => privTail_ok P A

end

/-! ## The call -/

/-- `out`, as the call writes it. -/
abbrev outR (s : State) : Region := ⟨s.gpr .a0, kk s⟩

/-- The regions the call reads (with `pc`, `pre` too) and writes. -/
abbrev callRd (pc : Bool) (s : State) : List Region :=
  [nR s, eR s, emR s, pR s, qR s, dpR s, dqR s, qiR s] ++ (if pc then [preR s] else []) ++ [PB pc s]
abbrev callWr (s : State) : List Region := [outR s, rsR s]

/-- The call's narrowed entry state. -/
abbrev callE (pc : Bool) (s t : State) : State := t.callEntry.withRegions (callRd pc s) (callWr s)

theorem callE_gpr (pc : Bool) (s t : State) {r : Reg} (hr : r ∉ linkRegs := by decide) :
    (callE pc s t).gpr r = t.gpr r :=
  State.callEntry_gpr t hr

theorem callE_stackArg {pc : Bool} {s t : State} {em : List Byte} (A : AtPriv pc s em t) {i : Nat}
    (hi : i < (if pc then 14 else 12)) : stackArg (callE pc s t) i = psa s i := by
  show t.mem.readW (stackArgAddr (callE pc s t) i) 64 = _
  rw [stackArgAddr, show (callE pc s t).sp = pb pc s from A.sp]
  by_cases h : i < 12
  · exact A.psa i h
  · cases pc with
    | false => exact absurd hi (by simp only [Bool.false_eq_true, ↓reduceIte]; omega)
    | true => exact A.psx rfl i (by omega) (by simpa using hi)

theorem priv_sdepth : sdepth Impl.Rsa.RISCV64.Priv.code = Impl.Rsa.RISCV64.Priv.frameBytes := by decide +kernel
theorem privP_sdepth : sdepth Impl.Rsa.RISCV64.Priv.codeP = Impl.Rsa.RISCV64.Priv.frameBytes := by decide +kernel

section
variable {pc : Bool} {D : Nat} {s : State} (P : PreS pc D s)
include P

theorem out_eq : outR s = oR s := by simp only [outR, oR, kk, P.ok]

theorem preP_at {t : State} {em : List Byte} (A : AtPriv pc s em t) : Rsa.RISCV64.Priv.PreP pc (callE pc s t) := by
  have hk : kk s ≤ 1024 := P.k2
  have sa := fun i (hi : i < 12) => callE_stackArg A (i := i) (Nat.lt_of_lt_of_le hi (by cases pc <;> decide))
  have hsp : (callE pc s t).sp = pb pc s := A.sp
  have g0 : (callE pc s t).gpr .a0 = s.gpr .a0 := (callE_gpr pc s t).trans A.a0
  have g1 : (callE pc s t).gpr .a1 = s.gpr .a3 := (callE_gpr pc s t).trans A.a1
  have g2 : (callE pc s t).gpr .a2 = s.gpr .a2 := (callE_gpr pc s t).trans A.a2
  have g3 : (callE pc s t).gpr .a3 = s.gpr .a3 := (callE_gpr pc s t).trans A.a3
  have g4 : (callE pc s t).gpr .a4 = s.gpr .a4 := (callE_gpr pc s t).trans A.a4
  have g5 : (callE pc s t).gpr .a5 = s.gpr .a5 := (callE_gpr pc s t).trans A.a5
  have g6 : (callE pc s t).gpr .a6 = off (Ss s) 0 := (callE_gpr pc s t).trans A.a6
  have g7 : (callE pc s t).gpr .a7 = s.gpr .a3 := (callE_gpr pc s t).trans A.a7
  have s0 : stackArg (callE pc s t) 0 = s.gpr .a6 := sa 0 (by decide)
  have s1 : stackArg (callE pc s t) 1 = s.gpr .a7 := sa 1 (by decide)
  have s2 : stackArg (callE pc s t) 2 = stackArg s 0 := sa 2 (by decide)
  have s3 : stackArg (callE pc s t) 3 = stackArg s 1 := sa 3 (by decide)
  have s4 : stackArg (callE pc s t) 4 = stackArg s 2 := sa 4 (by decide)
  have s5 : stackArg (callE pc s t) 5 = stackArg s 3 := sa 5 (by decide)
  have s6 : stackArg (callE pc s t) 6 = stackArg s 4 := sa 6 (by decide)
  have s7 : stackArg (callE pc s t) 7 = stackArg s 5 := sa 7 (by decide)
  have s8 : stackArg (callE pc s t) 8 = stackArg s 6 := sa 8 (by decide)
  have s9 : stackArg (callE pc s t) 9 = stackArg s 7 := sa 9 (by decide)
  have s10 : stackArg (callE pc s t) 10 = Ss s + BitVec.ofNat 64 oRsa := sa 10 (by decide)
  have s11 : stackArg (callE pc s t) 11 = BitVec.ofNat 64 ((stackArg s 13).toNat - 1024) := sa 11 (by decide)
  have hl : 1024 ≤ (stackArg s 13).toNat := by have := scLen P; unfold oRsa at this; omega
  have l11 : (stackArg (callE pc s t) 11).toNat = (stackArg s 13).toNat - 1024 := by
    rw [s11, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := (stackArg s 13).isLt; omega)
  have hO : Rsa.RISCV64.Priv.oR (callE pc s t) = oR s := by simp only [Rsa.RISCV64.Priv.oR, g0, g1, oR, P.ok]
  have hN : Rsa.RISCV64.Priv.nR (callE pc s t) = nR s := by simp only [Rsa.RISCV64.Priv.nR, g2, g3]
  have hE : Rsa.RISCV64.Priv.eR (callE pc s t) = eR s := by simp only [Rsa.RISCV64.Priv.eR, g4, g5]
  have hI : Rsa.RISCV64.Priv.iR (callE pc s t) = emR s := by simp only [Rsa.RISCV64.Priv.iR, g6, g7, emR, kk]
  have hP : Rsa.RISCV64.Priv.pR (callE pc s t) = pR s := by simp only [Rsa.RISCV64.Priv.pR, s0, s1]
  have hQ : Rsa.RISCV64.Priv.qR (callE pc s t) = qR s := by simp only [Rsa.RISCV64.Priv.qR, s2, s3]
  have hDP : Rsa.RISCV64.Priv.dpR (callE pc s t) = dpR s := by simp only [Rsa.RISCV64.Priv.dpR, s4, s5]
  have hDQ : Rsa.RISCV64.Priv.dqR (callE pc s t) = dqR s := by simp only [Rsa.RISCV64.Priv.dqR, s6, s7]
  have hQI : Rsa.RISCV64.Priv.qiR (callE pc s t) = qiR s := by simp only [Rsa.RISCV64.Priv.qiR, s8, s9]
  have hS : Rsa.RISCV64.Priv.sR (callE pc s t) = rsR s := by simp only [Rsa.RISCV64.Priv.sR, s10, l11]
  have hA : Rsa.RISCV64.Priv.aR pc (callE pc s t) = PB pc s := by
    simp only [Rsa.RISCV64.Priv.aR, stackArgAddr, hsp, Nat.mul_zero, BitVec.add_zero]; cases pc <;> rfl
  have hK : Rsa.RISCV64.Priv.kR (callE pc s t) = pkR pc s := by
    show Region.mk ((callE pc s t).sp - BitVec.ofNat 64 Impl.Rsa.RISCV64.Priv.frameBytes) _ = _
    rw [hsp, pb_kb P]; exact congrArg (Region.mk · _) (BitVec.add_sub_cancel _ _)
  have es := em_sub P
  have rs := rs_sub P
  have ks : Region.Sub (pkR pc s) (kS pc s) := pk_sub
  have pbs := PB_sub P
  have pt := kb_toNat P
  have spl := s.sp.isLt
  have st := P.sp1
  rw [stackBytes_split] at pt st
  unfold frameBytes Impl.Rsa.RISCV64.Priv.frameBytes at pt st
  have pr := privBytes_rng pc
  have pbt : (pb pc s).toNat = s.sp.toNat - (privBytes pc + 128) := by
    have := pb_kb P
    rw [this, Offset.toNat_add_ofNat, kb_toNat P, stackBytes_split]
    unfold frameBytes Impl.Rsa.RISCV64.Priv.frameBytes at *; omega
  have e11 : (Ss s).toNat = (stackArg s 12).toNat := rfl
  have hsw := P.hs
  unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hsw
  have sdt : (Ss s + BitVec.ofNat 64 oRsa).toNat = (Ss s).toNat + oRsa := by
    rw [Offset.toNat_add_ofNat]; have := P.wsc; unfold oRsa at *; omega
  have ek : kk s = (s.gpr .a3).toNat := rfl
  exact {
    sp16 := by rw [hsp]; exact pb_al P
    sp1 := by rw [hsp, pbt]; unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega
    sp2 := by rw [hsp, pbt]; omega
    hrd := by
      rw [Rsa.RISCV64.Priv.rdL, hN, hE, hI, hP, hQ, hDP, hDQ, hQI, hA]
      cases pc with
      | false => rfl
      | true =>
        have hPre : Rsa.RISCV64.Priv.preR (callE true s t) = preR s := by
          simp only [Rsa.RISCV64.Priv.preR, callE_stackArg A (i := 12) (by decide),
            callE_stackArg A (i := 13) (by decide), psa]
        simp only [↓reduceIte, hPre]; rfl
    hwr := by rw [hO, hS, ← out_eq P]; rfl
    on := by rw [hO, hN]; exact P.on
    oe := by rw [hO, hE]; exact P.oe
    oi := by rw [hO, hI]; exact P.os.sub_right es
    op := by rw [hO, hP]; exact P.op
    oq := by rw [hO, hQ]; exact P.oq
    odp := by rw [hO, hDP]; exact P.odp
    odq := by rw [hO, hDQ]; exact P.odq
    oqi := by rw [hO, hQI]; exact P.oqi
    os := by rw [hO, hS]; exact P.os.sub_right rs
    oa := by rw [hO, hA]; exact (P.ko.sub_left pbs).symm
    ns := by rw [hN, hS]; exact P.ns.sub_right rs
    es := by rw [hE, hS]; exact P.es.sub_right rs
    is := by rw [hI, hS]; exact em_rs P
    ps := by rw [hP, hS]; exact P.ps.sub_right rs
    qs := by rw [hQ, hS]; exact P.qs.sub_right rs
    dps := by rw [hDP, hS]; exact P.dps.sub_right rs
    dqs := by rw [hDQ, hS]; exact P.dqs.sub_right rs
    qis := by rw [hQI, hS]; exact P.qis.sub_right rs
    sa := by rw [hS, hA]; exact ((P.ks.sub_left pbs).sub_right rs).symm
    ko := by rw [hK, hO]; exact P.ko.sub_left ks
    kn := by rw [hK, hN]; exact P.kn.sub_left ks
    ke := by rw [hK, hE]; exact P.ke.sub_left ks
    ki := by rw [hK, hI]; exact (P.ks.sub_left ks).sub_right es
    kp := by rw [hK, hP]; exact P.kp.sub_left ks
    kq := by rw [hK, hQ]; exact P.kq.sub_left ks
    kdp := by rw [hK, hDP]; exact P.kdp.sub_left ks
    kdq := by rw [hK, hDQ]; exact P.kdq.sub_left ks
    kqi := by rw [hK, hQI]; exact P.kqi.sub_left ks
    ks := by rw [hK, hS]; exact (P.ks.sub_left ks).sub_right rs
    ka := by rw [hK, hA]; exact pk_PB P
    wo := by rw [g0, g1]; have := P.wo; rw [P.ok] at this; exact this
    wn := by rw [g2, g3]; exact P.wn
    we := by rw [g4, g5]; exact P.we
    wi := by
      rw [g6, g7]
      show (Ss s + BitVec.ofNat 64 0).toNat + _ ≤ _
      rw [BitVec.add_zero, e11]; have := P.wsc; have := scLen P; unfold oRsa at *; omega
    wp := by rw [s0, s1]; exact P.wp
    wq := by rw [s2, s3]; exact P.wq
    wdp := by rw [s4, s5]; exact P.wdp
    wdq := by rw [s6, s7]; exact P.wdq
    wqi := by rw [s8, s9]; exact P.wqi
    ws := by rw [s10, l11, sdt, e11]; have := P.wsc; unfold oRsa; omega
    k1 := by rw [g3]; exact P.k1
    k2 := by rw [g3]; exact P.k2
    h1 := by rw [g1, g3]
    h7 := by rw [g7, g3]
    e1 := by rw [g5]; exact P.e1
    e2 := by rw [g5, g3]; exact P.e2
    p1 := by rw [s1]; exact P.p1
    p2 := by rw [s1, g3]; exact P.p2
    q1 := by rw [s3]; exact P.q1
    q2 := by rw [s3, g3]; exact P.q2
    h5 := by rw [s5, s1]; exact P.h3
    h9 := by rw [s9, s1]; exact P.h7
    h7' := by rw [s7, s3]; exact P.h5
    hs := by rw [g3, l11]; unfold Spec.Rsa.scratchWords; omega
    al := by rw [s10, sdt, e11]; have := P.als; unfold oRsa; omega }

theorem cov_sc {d n : Nat} (h : d + n ≤ (stackArg s 13).toNat * 8) {rs : List Region} :
    Covers [⟨Ss s + BitVec.ofNat 64 d, n⟩] (rs ++ s.wr) :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr, P.hwr]
    exact ⟨scR s, by simp, d, rfl, h⟩

theorem call_covers {t : State} {em : List Byte} (A : AtPriv pc s em t) :
    Covers (callRd pc s ++ callWr s) (t.rd ++ t.wr) ∧ Covers (callWr s) t.wr := by
  have hsw := P.hs
  have : kk s ≤ 1024 := P.k2
  unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hsw
  have hw : Covers (callWr s) t.wr := by
    rw [A.wr]
    refine Covers.pair ?_ ?_
    · rw [out_eq P]
      exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, P.hwr]; simp
    · exact cov_sc P (d := oRsa) (rs := [PB pc s, fr s]) (by unfold oRsa; omega)
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  rw [A.rd, A.wr, P.hrd]
  have inRd : ∀ {r}, r ∈ rdS pc D s → Covers [r] (rdS pc D s ++ (PB pc s :: fr s :: s.wr)) := fun h =>
    Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact h)
  simp only [callRd, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hp) | rfl
  · exact inRd (by simp)
  · exact inRd (by simp)
  · exact Covers.right (cov_sc P (d := 0) (n := kk s) (rs := [PB pc s, fr s]) (by unfold kk at *; omega))
  · exact inRd (by simp)
  · exact inRd (by simp)
  · exact inRd (by simp)
  · exact inRd (by simp)
  · exact inRd (by simp)
  · cases pc with
    | false => simp at hp
    | true =>
      simp only [↓reduceIte, List.mem_singleton] at hp
      subst hp; exact inRd (by simp)
  · exact Covers.right (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)

omit P in
/-- The caller's buffers at the call are as on entry. -/
theorem bytes_at {t : State} {em : List Byte} (A : AtPriv pc s em t) {R : Region} (hd : (kS pc s).Disjoint R)
    (hs : (SC Ss s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
  VG.Proof.RsaOaep.RISCV64.bytes_entry A.mem hd hs hl

theorem below_pb : below (pb pc s) Impl.Rsa.RISCV64.Priv.frameBytes = pkR pc s := by
  show Region.mk (pb pc s - BitVec.ofNat 64 Impl.Rsa.RISCV64.Priv.frameBytes) _ = _
  rw [pb_kb P]; exact congrArg (Region.mk · _) (BitVec.add_sub_cancel _ _)

/-- Our frame's slots and what the call writes. -/
theorem slots_dis : ∀ r ∈ callWr s ++ [pkR pc s],
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 Proof.RsaOaep.RISCV64.oSv, frameBytes - Proof.RsaOaep.RISCV64.oSv⟩ r := by
  have pr := privBytes_rng pc
  have hk : Region.Sub ⟨fb s + BitVec.ofNat 64 Proof.RsaOaep.RISCV64.oSv,
      frameBytes - Proof.RsaOaep.RISCV64.oSv⟩ (kS pc s) := by
    rw [fb_kb P, Offset.add_add]
    exact kb_sub (by
      rw [stackBytes_split]; unfold frameBytes Impl.Rsa.RISCV64.Priv.frameBytes Proof.RsaOaep.RISCV64.oSv; omega)
  intro r hr
  simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [out_eq P]; exact P.ko.sub_left hk
  · exact (P.ks.sub_left hk).sub_right (rs_sub P)
  · rw [fb_kb P, Offset.add_add]
    exact Offset.disjoint_base _ (by unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega)
      (by unfold frameBytes Proof.RsaOaep.RISCV64.oSv Impl.Rsa.RISCV64.Priv.frameBytes; omega)

omit P in
/-- With `pc`, the facts of `pre` at the call. -/
theorem preX_at {t : State} {em : List Byte} (P' : PreS true D s) (X : PreXS s) (A : AtPriv true s em t) :
    Rsa.RISCV64.Priv.PreX (callE true s t) := by
  have sa := fun i (hi : i < 14) => callE_stackArg A (i := i) (by simpa using hi)
  have hsp : (callE true s t).sp = pb true s := A.sp
  have hpbt : (pb true s).toNat = s.sp.toNat - 240 := by
    have := pb_kb P'
    have sp1 := P'.sp1
    rw [this, Offset.toNat_add_ofNat, kb_toNat P', stackBytes_true]
    rw [stackBytes_true] at sp1; omega
  have hPre : Rsa.RISCV64.Priv.preR (callE true s t) = preR s := by
    simp only [Rsa.RISCV64.Priv.preR, sa 12 (by decide), sa 13 (by decide), psa]
  have hO : Rsa.RISCV64.Priv.oR (callE true s t) = oR s := by
    simp only [Rsa.RISCV64.Priv.oR, callE_gpr true s t (r := .a0), callE_gpr true s t (r := .a1), A.a0, A.a1, oR,
      P'.ok]
  have hl : 1024 ≤ (stackArg s 13).toNat := by
    have := P'.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega
  have w11 : (BitVec.ofNat 64 ((stackArg s 13).toNat - 1024)).toNat = (stackArg s 13).toNat - 1024 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (stackArg s 13).isLt; omega)]
  have hS : Rsa.RISCV64.Priv.sR (callE true s t) = rsR s := by
    simp only [Rsa.RISCV64.Priv.sR, sa 10 (by decide), sa 11 (by decide), psa, w11]
  have hK : Rsa.RISCV64.Priv.kR (callE true s t) = pkR true s := by
    show Region.mk ((callE true s t).sp - BitVec.ofNat 64 Impl.Rsa.RISCV64.Priv.frameBytes) _ = _
    rw [hsp, pb_kb P']; exact congrArg (Region.mk · _) (BitVec.add_sub_cancel _ _)
  refine ⟨by rw [hO, hPre]; exact X.oP, by rw [hS, hPre]; exact X.sP.sub_left (rs_sub P'),
    by rw [hK, hPre]; exact X.kP.sub_left pk_sub, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sa 12 (by decide), sa 13 (by decide)]; exact X.wP
  · rw [sa 13 (by decide), sa 1 (by decide), sa 3 (by decide), callE_gpr true s t (r := .a3), A.a3]; exact X.pl
  · rw [hsp, hpbt]; have := P'.sp1; rw [stackBytes_true] at this; omega
  · -- `pre`'s values, as the caller's precondition gives them.
    have hb := fun {p : Addr} {len : Nat} (hd : (kS true s).Disjoint ⟨p, len⟩) (hs : (scR s).Disjoint ⟨p, len⟩)
      (hl : len ≤ 2 ^ 64) => bytes_at A (R := ⟨p, len⟩) hd (hs.sub_left (sc_sub P')) hl
    have hw := VG.Proof.Rsa.RISCV64.Priv.words_of_frame A.mem (p := stackArg s 16) (n := (stackArg s 17).toNat)
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [Nat.mul_comm]; exact X.kP.symm
        · rw [Nat.mul_comm]; exact (X.sP.sub_left (sc_sub P')).symm) (by have := X.wP; omega)
    simp only [Rsa.RISCV64.Priv.PreHyp, State.withRegions_mem, State.callEntry_mem, callE_gpr true s t (r := .a2),
      callE_gpr true s t (r := .a3), A.a2, A.a3, sa 0 (by decide), sa 1 (by decide), sa 2 (by decide),
      sa 3 (by decide), sa 12 (by decide), sa 13 (by decide), psa, hw]
    rw [hb P'.kn P'.ns.symm (by have := P'.wn; omega), hb P'.kp P'.ps.symm (by have := P'.wp; omega),
      hb P'.kq P'.qs.symm (by have := P'.wq; omega)]
    exact X.hyp rfl
  · rw [sa 12 (by decide)]; exact X.alP

/-- The call of `vg_rsa_private_checked`, or with `pc` of
`vg_rsa_private_checked_precomputed`. -/
theorem call_priv {u : State} {em : List Byte} (A : AtPriv pc s em u) :
    WP isa (privCall pc) u fun v => v.rd = u.rd ∧ v.wr = u.wr ∧ v.sp = u.sp ∧
      Frame (callWr s ++ [pkR pc s]) u.mem v.mem ∧
      Rsa.RISCV64.Priv.fnPost (callE pc s u) (v.withRegions (callRd pc s) (callWr s)) := by
  obtain ⟨hc, hw⟩ := call_covers P A
  cases pc with
  | false =>
    refine WP.callAny (k := Rsa.RISCV64.Priv.fnContract) Rsa.RISCV64.Priv.code_correct
      (Rsa.RISCV64.Priv.pre_of_preP (preP_at P A)) hc hw (fun v hrd hwr hsp' hf _ hpost => ?_)
      (by rw [priv_sdepth]; decide)
    rw [priv_sdepth, A.sp, below_pb P] at hf
    exact ⟨hrd, hwr, hsp', hf, hpost⟩
  | true =>
    refine WP.callAny (k := Rsa.RISCV64.Priv.fnContractP) Rsa.RISCV64.Priv.codeP_correct
      (Rsa.RISCV64.Priv.pre_of_prePX (preP_at P A) (preX_at P (P.px rfl) A)) hc hw
      (fun v hrd hwr hsp' hf _ hpost => ?_) (by rw [privP_sdepth]; decide)
    rw [privP_sdepth, A.sp, below_pb P] at hf
    exact ⟨hrd, hwr, hsp', hf, hpost⟩

/-- After the private operation. -/
def AfterS (s : State) (em : List Byte) (w : State) : Prop :=
  Saves s w ∧ w.rd = s.rd ∧
    Spec.Rsa.writtenOutcome w.mem (s.gpr .a0) (kk s) ((w.gpr .a0).setWidth 32) (privOut s em)

theorem priv_ok {t : State} (h : Base Ss vS s t) (sp : Spilled s t.mem)
    {em : List Byte} (hem : Spec.Rsa.bytesAt t.mem (off (Ss s) 0) (kk s) = em) :
    WP isa (priv pc) t (AfterS s em) := by
  have hsp : t.sp = fb s := h.sp
  have pr := privBytes_rng pc
  unfold priv
  refine WP.alloc (by cases pc <;> exact ⟨by decide, by decide, by decide⟩) (by
    rw [hsp]; have := P.sp1
    rw [stackBytes_split] at this
    simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat, frameBytes, Impl.Rsa.RISCV64.Priv.frameBytes] at *
    omega) ?_
  refine WP.seq (WP.mono (privArgs_ok P h sp hem) fun u A => ?_)
  refine WP.mono (call_priv P A) fun v ⟨hrd, hwr, hsp', hf, hpost⟩ => ?_
  -- The outcome.
  have sa := fun i (hi : i < 12) => callE_stackArg A (i := i) (Nat.lt_of_lt_of_le hi (by cases pc <;> decide))
  have s0 : stackArg (callE pc s u) 0 = s.gpr .a6 := sa 0 (by decide)
  have s1 : stackArg (callE pc s u) 1 = s.gpr .a7 := sa 1 (by decide)
  have s2 : stackArg (callE pc s u) 2 = stackArg s 0 := sa 2 (by decide)
  have s3 : stackArg (callE pc s u) 3 = stackArg s 1 := sa 3 (by decide)
  have s4 : stackArg (callE pc s u) 4 = stackArg s 2 := sa 4 (by decide)
  have s6 : stackArg (callE pc s u) 6 = stackArg s 4 := sa 6 (by decide)
  have s8 : stackArg (callE pc s u) 8 = stackArg s 6 := sa 8 (by decide)
  simp only [Rsa.RISCV64.Priv.fnPost, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_mem, callE_gpr pc s u (r := .a0), callE_gpr pc s u (r := .a2), callE_gpr pc s u (r := .a3),
    callE_gpr pc s u (r := .a4), callE_gpr pc s u (r := .a5), callE_gpr pc s u (r := .a6), A.a0, A.a2, A.a3, A.a4,
    A.a5, A.a6, s0, s1, s2, s3, s4, s6, s8] at hpost
  have hb := fun {p : Addr} {len : Nat} (hd : (kS pc s).Disjoint ⟨p, len⟩) (hs : (scR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) => bytes_at A (R := ⟨p, len⟩) hd (hs.sub_left (sc_sub P)) hl
  rw [A.em, hb P.kn P.ns.symm (by have := P.wn; omega), hb P.ke P.es.symm (by have := P.we; omega),
    hb P.kp P.ps.symm (by have := P.wp; omega), hb P.kq P.qs.symm (by have := P.wq; omega),
    hb (by have := P.kdp; simp only [dpR, P.h3] at this; exact this)
      (by have := P.dps; simp only [dpR, P.h3] at this; exact this.symm) (by have := P.wdp; rw [P.h3] at this; omega),
    hb (by have := P.kdq; simp only [dqR, P.h5] at this; exact this)
      (by have := P.dqs; simp only [dqR, P.h5] at this; exact this.symm) (by have := P.wdq; rw [P.h5] at this; omega),
    hb (by have := P.kqi; simp only [qiR, P.h7] at this; exact this)
      (by have := P.qis; simp only [qiR, P.h7] at this; exact this.symm) (by have := P.wqi; rw [P.h7] at this; omega)]
    at hpost
  -- The state after the frame's release.
  have fsp : (freed (privBytes pc) v).sp = fb s := by
    show v.sp + BitVec.ofNat 64 (privBytes pc) = fb s
    rw [hsp', A.sp, BitVec.sub_add_cancel]
  have fwr : (freed (privBytes pc) v).wr = fr s :: s.wr := by
    show v.wr.tail = _; rw [hwr, A.wr]; rfl
  have svs : Spill.Saved (fb s) s.gpr saved v.mem :=
    A.sv.frame_in (lo := Proof.RsaOaep.RISCV64.oSv) (n := frameBytes - Proof.RsaOaep.RISCV64.oSv)
      (fun p hp => by
        have := Proof.RsaOaep.RISCV64.saved_offs p hp; unfold frameBytes Proof.RsaOaep.RISCV64.oSv at *; omega)
      hf (slots_dis P)
  exact ⟨⟨fsp, fwr, svs⟩, by show v.rd = _; exact hrd.trans A.rd, hpost⟩

end

end VG.Proof.RsaPss.RISCV64.Sg
