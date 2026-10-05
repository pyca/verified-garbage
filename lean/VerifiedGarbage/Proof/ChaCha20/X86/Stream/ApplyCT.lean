import VerifiedGarbage.Proof.ChaCha20.X86.Stream.Init
import VerifiedGarbage.Proof.ChaCha20.X86.Variant
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.RelCT

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.X86.Stream.Calls`. -/
section

/-!
# Streaming ChaCha20 on x86 (32-bit): the entry state and the calls

Untrusted: everything here is checked by Lean. The contract of `apply`, what
its precondition gives, and the calls of `vg_chacha20_block` and
`vg_chacha20_xor`, each in a frame of its arguments (`WP.callWith`), from
their proofs of correctness, as ChaCha20-Poly1305 makes them: what they need
of the state they are called from (`CallPre`), and what holds when they
return.
-/

namespace VG.Proof.ChaCha20

open VG.X86
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt)

/-- x86 (32-bit) contract for `vg_chacha20_apply(state, data, len) -> eax`,
whose arguments are on the stack (cdecl), with 32 bytes of stack below the
return address (the frames, return addresses and stack of the calls). -/
def applyX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 768⟩
    let data : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 32, 32⟩
    s.rd = [] ∧ s.wr = [state, data, args] ∧ state.Disjoint data ∧
    args.Disjoint state ∧ args.Disjoint data ∧ ret.Disjoint state ∧ ret.Disjoint data ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧
    (arg s 0).toNat + 768 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
    32 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s s' :=
    keyAt s'.mem ((arg s 0).setWidth 64) = keyAt s.mem ((arg s 0).setWidth 64) ∧
      if (arg s 2).toNat ≤ leftAt s.mem ((arg s 0).setWidth 64) then
        s'.gpr .eax = 1 ∧
          bytesAt s'.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
            List.zipWith (· ^^^ ·) (bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
              ((restAt s.mem ((arg s 0).setWidth 64)).take (arg s 2).toNat) ∧
          restAt s'.mem ((arg s 0).setWidth 64) = (restAt s.mem ((arg s 0).setWidth 64)).drop (arg s 2).toNat
      else
        s'.gpr .eax = 0 ∧
          bytesAt s'.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
            bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat ∧
          restAt s'.mem ((arg s 0).setWidth 64) = restAt s.mem ((arg s 0).setWidth 64)
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧
      [leftAt s₁.mem ((arg s₁ 0).setWidth 64)] = [leftAt s₂.mem ((arg s₂ 0).setWidth 64)]

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.X86.Stream

open VG VG.X86 VG.Impl.ChaCha20.X86.Stream
open VG.Impl.ChaCha20.X86 (at_)
open VG.Proof.ChaCha20.X86 (contains_off XorImpl)
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt stateAt keystream serialize block)

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev E : BitVec 32 := s₀.gpr .esp
abbrev DP : BitVec 32 := arg s₀ 1
abbrev LN : BitVec 32 := arg s₀ 2
abbrev L : Nat := (VG.Proof.ChaCha20.X86.Stream.LN s₀).toNat
abbrev dp : Addr := (VG.Proof.ChaCha20.X86.Stream.DP s₀).setWidth 64
/-- The number of bytes of keystream left, and those in the buffered block. -/
abbrev N : Nat := leftAt s₀.mem (st s₀)
abbrev O : Nat := VG.Proof.ChaCha20.X86.Stream.N s₀ % 64
/-- The bytes from the buffered block, the whole blocks and the bytes of the
next block that `apply` uses. -/
abbrev H : Nat := headLen s₀.mem (st s₀) (VG.Proof.ChaCha20.X86.Stream.L s₀)
abbrev NB : Nat := blocksOf s₀.mem (st s₀) (VG.Proof.ChaCha20.X86.Stream.L s₀)
abbrev T : Nat := tailLen s₀.mem (st s₀) (VG.Proof.ChaCha20.X86.Stream.L s₀)
abbrev S0 : CState := stateAt s₀.mem (st s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (VG.Proof.ChaCha20.X86.Stream.dp s₀ + BitVec.ofNat 64 k)
abbrev stR : Region := ⟨st s₀, 768⟩
abbrev dR : Region := ⟨VG.Proof.ChaCha20.X86.Stream.dp s₀, VG.Proof.ChaCha20.X86.Stream.L s₀⟩
abbrev aR : Region := ⟨argAddr s₀ 0, 12⟩
abbrev retR : Region := ⟨(VG.Proof.ChaCha20.X86.Stream.E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (VG.Proof.ChaCha20.X86.Stream.E s₀) 32
/-- The keystream byte XORed into byte `k` of the data. -/
abbrev KS (k : Nat) : Byte :=
  if k < VG.Proof.ChaCha20.X86.Stream.H s₀ then s₀.mem (st s₀ + BitVec.ofNat 64 (128 - VG.Proof.ChaCha20.X86.Stream.O s₀ + k))
  else (serialize (block (ctr (VG.Proof.ChaCha20.X86.Stream.S0 s₀) ((k - VG.Proof.ChaCha20.X86.Stream.H s₀) / 64)))).getD ((k - VG.Proof.ChaCha20.X86.Stream.H s₀) % 64) 0
/-- The data with its first `j` bytes XORed. -/
abbrev Done (j : Nat) (m : Mem) : Prop :=
  ∀ k < VG.Proof.ChaCha20.X86.Stream.L s₀, m (VG.Proof.ChaCha20.X86.Stream.dp s₀ + BitVec.ofNat 64 k) = if k < j then VG.Proof.ChaCha20.X86.Stream.D0 s₀ k ^^^ VG.Proof.ChaCha20.X86.Stream.KS s₀ k else VG.Proof.ChaCha20.X86.Stream.D0 s₀ k
end

theorem L_lt (s₀ : State) : VG.Proof.ChaCha20.X86.Stream.L s₀ < 2 ^ 32 := (VG.Proof.ChaCha20.X86.Stream.LN s₀).isLt
theorem N_lt (s₀ : State) : VG.Proof.ChaCha20.X86.Stream.N s₀ < 2 ^ 64 := (s₀.mem.readW (st s₀ + 128) 64).isLt
theorem H_le (s₀ : State) : VG.Proof.ChaCha20.X86.Stream.H s₀ ≤ VG.Proof.ChaCha20.X86.Stream.L s₀ := Nat.min_le_right _ _
theorem H_le_O (s₀ : State) : VG.Proof.ChaCha20.X86.Stream.H s₀ ≤ VG.Proof.ChaCha20.X86.Stream.O s₀ := Nat.min_le_left _ _
theorem O_lt (s₀ : State) : VG.Proof.ChaCha20.X86.Stream.O s₀ < 64 := Nat.mod_lt _ (by decide)
theorem T_eq (s₀ : State) : VG.Proof.ChaCha20.X86.Stream.T s₀ = VG.Proof.ChaCha20.X86.Stream.L s₀ - VG.Proof.ChaCha20.X86.Stream.H s₀ - 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀ := by simp only [VG.Proof.ChaCha20.X86.Stream.T, VG.Proof.ChaCha20.X86.Stream.NB, tailLen, blocksOf, VG.Proof.ChaCha20.X86.Stream.H]; omega
theorem HNB_le (s₀ : State) : VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀ ≤ VG.Proof.ChaCha20.X86.Stream.L s₀ := by
  have := VG.Proof.ChaCha20.X86.Stream.H_le s₀; simp only [VG.Proof.ChaCha20.X86.Stream.NB, blocksOf, VG.Proof.ChaCha20.X86.Stream.H] at *; omega

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [VG.Proof.ChaCha20.X86.Stream.stR s₀, VG.Proof.ChaCha20.X86.Stream.dR s₀, VG.Proof.ChaCha20.X86.Stream.aR s₀]
  st_d : (VG.Proof.ChaCha20.X86.Stream.stR s₀).Disjoint (VG.Proof.ChaCha20.X86.Stream.dR s₀)
  a_st : (VG.Proof.ChaCha20.X86.Stream.aR s₀).Disjoint (VG.Proof.ChaCha20.X86.Stream.stR s₀)
  a_d : (VG.Proof.ChaCha20.X86.Stream.aR s₀).Disjoint (VG.Proof.ChaCha20.X86.Stream.dR s₀)
  ret_st : (VG.Proof.ChaCha20.X86.Stream.retR s₀).Disjoint (VG.Proof.ChaCha20.X86.Stream.stR s₀)
  ret_d : (VG.Proof.ChaCha20.X86.Stream.retR s₀).Disjoint (VG.Proof.ChaCha20.X86.Stream.dR s₀)
  stk_st : (VG.Proof.ChaCha20.X86.Stream.stkR s₀).Disjoint (VG.Proof.ChaCha20.X86.Stream.stR s₀)
  stk_d : (VG.Proof.ChaCha20.X86.Stream.stkR s₀).Disjoint (VG.Proof.ChaCha20.X86.Stream.dR s₀)
  st_fit : (ST s₀).toNat + 768 ≤ 2 ^ 32
  d_fit : (VG.Proof.ChaCha20.X86.Stream.DP s₀).toNat + VG.Proof.ChaCha20.X86.Stream.L s₀ ≤ 2 ^ 32
  sp_lo : 32 ≤ (VG.Proof.ChaCha20.X86.Stream.E s₀).toNat
  sp_hi : (VG.Proof.ChaCha20.X86.Stream.E s₀).toNat + 16 ≤ 2 ^ 32

theorem APre.of (s₀ : State) (h : Proof.ChaCha20.applyX86.pre s₀) : VG.Proof.ChaCha20.X86.Stream.APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  have e : (s₀.gpr .esp).setWidth 64 - 32 = (VG.Proof.ChaCha20.X86.Stream.E s₀ - BitVec.ofNat 32 32).setWidth 64 :=
    (VG.X86.Taint.sub_setWidth h12).symm
  rw [e] at h8 h9
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

namespace APre
variable {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀)
include hp

theorem eaS {d : Nat} (hd : d < 768) : (ST s₀ + BitVec.ofNat 32 d).setWidth 64 = st s₀ + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.st_fit; omega)

theorem sNat {d : Nat} (hd : d < 768) : (ST s₀ + BitVec.ofNat 32 d).toNat = (ST s₀).toNat + d := by
  have := hp.st_fit
  rw [BitVec.toNat_add, Proof.ChaCha20.X86.Bytes.toNat_ofNat_lt32 (by omega), Nat.mod_eq_of_lt (by omega)]

theorem eaD {d : Nat} (hd : d < VG.Proof.ChaCha20.X86.Stream.L s₀) : (VG.Proof.ChaCha20.X86.Stream.DP s₀ + BitVec.ofNat 32 d).setWidth 64 = VG.Proof.ChaCha20.X86.Stream.dp s₀ + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.d_fit; omega)

theorem dNat {d : Nat} (hd : d < VG.Proof.ChaCha20.X86.Stream.L s₀) : (VG.Proof.ChaCha20.X86.Stream.DP s₀ + BitVec.ofNat 32 d).toNat = (VG.Proof.ChaCha20.X86.Stream.DP s₀).toNat + d := by
  have := hp.d_fit
  have := VG.Proof.ChaCha20.X86.Stream.L_lt s₀
  rw [BitVec.toNat_add, Proof.ChaCha20.X86.Bytes.toNat_ofNat_lt32 (by omega), Nat.mod_eq_of_lt (by omega)]

theorem w_st {d n : Nat} (h : d + n ≤ 768) : InRegions s₀.wr (st s₀ + BitVec.ofNat 64 d) n :=
  ⟨VG.Proof.ChaCha20.X86.Stream.stR s₀, by rw [hp.wr]; exact List.mem_cons_self .., contains_off h (by omega)⟩

theorem r_st {d n : Nat} (h : d + n ≤ 768) : InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 d) n := by
  rw [hp.rd, List.nil_append]; exact hp.w_st h

theorem in_arg {i : Nat} (hi : i < 3) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨VG.Proof.ChaCha20.X86.Stream.aR s₀, by rw [hp.rd, hp.wr]; simp, arg_in s₀ (n := 3) (by have := hp.sp_hi; omega) hi⟩

theorem E64 {n : Nat} (hn : n ≤ 32) :
    (VG.Proof.ChaCha20.X86.Stream.E s₀ - BitVec.ofNat 32 n).setWidth 64 = (VG.Proof.ChaCha20.X86.Stream.E s₀).setWidth 64 - BitVec.ofNat 64 n :=
  VG.X86.Taint.sub_setWidth (by have := hp.sp_lo; omega)

/-- Part of the stack below the return address. -/
theorem stk_part {a n : Nat} (h : n ≤ a) (ha : a ≤ 32) :
    Region.Sub ⟨(VG.Proof.ChaCha20.X86.Stream.E s₀ - BitVec.ofNat 32 a).setWidth 64, n⟩ (VG.Proof.ChaCha20.X86.Stream.stkR s₀) :=
  fun x hx => below_sub ha hp.sp_lo x (Region.sub_prefix h x hx)

end APre

theorem d_ne_st {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) {j k : Nat} (hj : j < VG.Proof.ChaCha20.X86.Stream.L s₀) (hk : k < 768) :
    VG.Proof.ChaCha20.X86.Stream.dp s₀ + BitVec.ofNat 64 j ≠ st s₀ + BitVec.ofNat 64 k := by
  intro he
  have c₁ : (VG.Proof.ChaCha20.X86.Stream.dR s₀).Contains (VG.Proof.ChaCha20.X86.Stream.dp s₀ + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ (by omega) (by have := VG.Proof.ChaCha20.X86.Stream.L_lt s₀; omega)
  have c₂ : (VG.Proof.ChaCha20.X86.Stream.stR s₀).Contains (st s₀ + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega) (by omega)
  rw [he] at c₁
  exact hp.st_d _ c₂ c₁

theorem not_in_prefix (p : Addr) {k c : Nat} (hk : c ≤ k) (hk' : k < 2 ^ 64) :
    ¬ (⟨p, c⟩ : Region).Contains (p + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat p hk']
  omega

theorem prefix_sub (p : Addr) {c n : Nat} (h : c ≤ n) : Region.Sub ⟨p, c⟩ ⟨p, n⟩ := Region.sub_prefix h

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-! ## The state a call is made from -/

structure At (s₀ s : State) : Prop where
  esp : s.gpr .esp = VG.Proof.ChaCha20.X86.Stream.E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

section
variable {s₀ s : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) (h : VG.Proof.ChaCha20.X86.Stream.At s₀ s) {rs : List Reg} (hk : rs.length ≤ 4)
include hp h hk

theorem At.fit : 4 * rs.length + 4 ≤ (s.gpr .esp).toNat := by
  rw [h.esp]; have := hp.sp_lo; omega

omit hp hk in
theorem At.argAddr0 :
    argAddr (pushed rs s).callEntry 0 = (VG.Proof.ChaCha20.X86.Stream.E s₀ - BitVec.ofNat 32 (4 * rs.length)).setWidth 64 := by
  rw [callEntry_argAddr0, h.esp]

omit hp hk in
theorem At.esp64 :
    ((pushed rs s).callEntry.gpr .esp).setWidth 64 =
      (VG.Proof.ChaCha20.X86.Stream.E s₀ - BitVec.ofNat 32 (4 * rs.length + 4)).setWidth 64 := by
  rw [callEntry_esp', h.esp]

theorem At.espNat : ((pushed rs s).callEntry.gpr .esp).toNat = (VG.Proof.ChaCha20.X86.Stream.E s₀).toNat - (4 * rs.length + 4) := by
  rw [callEntry_espNat (h.fit hp hk), h.esp]

/-- The call's frame and return address are on the stack below `esp`. -/
theorem At.entry_frame (hrs : Reg.esp ∉ rs) : Frame [VG.Proof.ChaCha20.X86.Stream.stkR s₀] s.mem (pushed rs s).callEntry.mem :=
  (callEntry_frame (h.fit hp hk) hrs).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by rw [h.esp]; exact below_sub (by omega) hp.sp_lo⟩

end

/-- A region at offset `o` within one of `rs'`. -/
theorem within {r : Region} {rs' : List Region} (r' : Region) (hr' : r' ∈ rs') (o : Nat)
    (hb : r.base = r'.base + BitVec.ofNat 64 o) (hl : o + r.len ≤ r'.len) :
    ∃ r' ∈ rs', ∃ o, r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len :=
  ⟨r', hr', o, hb, hl⟩

theorem block_nosp : NoSp Impl.ChaCha20.X86.block := NoSp.of_all (by lit_decide)
theorem block_stack : stackUse Impl.ChaCha20.X86.block = 0 := by lit_decide

/-! ## `vg_chacha20_block` -/

/-- The permissions it is called with. -/
abbrev rdBlk (s₀ : State) : List Region := [⟨st s₀, 64⟩, below (VG.Proof.ChaCha20.X86.Stream.E s₀) 8]
abbrev wrBlk (s₀ : State) : List Region := [⟨st s₀ + BitVec.ofNat 64 64, 256⟩]

theorem block_pre {s₀ s : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) (h : VG.Proof.ChaCha20.X86.Stream.At s₀ s) (hebx : s.gpr .ebx = ST s₀)
    (heax : s.gpr .eax = ST s₀ + BitVec.ofNat 32 64) :
    CallPre Proof.ChaCha20.blockX86 [.eax, .ebx] (VG.Proof.ChaCha20.X86.Stream.rdBlk s₀) (VG.Proof.ChaCha20.X86.Stream.wrBlk s₀) s := by
  have hk : [Reg.eax, .ebx].length ≤ 4 := by decide
  have fit := h.fit hp hk
  have a0 : arg (pushed [.eax, .ebx] s).callEntry 0 = ST s₀ := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hebx
  have a1 : arg (pushed [.eax, .ebx] s).callEntry 1 = ST s₀ + BitVec.ofNat 32 64 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact heax
  have e := hp.sp_lo
  have e₂ := hp.sp_hi
  have e' := hp.st_fit
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.ChaCha20.blockX86, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a1, h.argAddr0,
      h.esp64, h.espNat hp hk, hp.eaS (d := 64) (by decide), hp.sNat (d := 64) (by decide),
      List.length_cons, List.length_nil]
    refine ⟨trivial, trivial, Offset.disjoint_base _ (by omega) (by omega), ?_, ?_, by omega, by omega, by omega⟩
    · exact (hp.stk_st.sub_left (hp.stk_part (by decide) (by decide))).sub_right (Offset.sub_base _ (by omega))
    · exact (hp.stk_st.sub_left (hp.stk_part (by decide) (by decide))).sub_right (Offset.sub_base _ (by omega))
  · rw [h.esp, h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Proof.ChaCha20.X86.Stream.within (VG.Proof.ChaCha20.X86.Stream.stR s₀) (by simp) 0 (by simp) (by show 0 + 64 ≤ 768; omega)
    · exact VG.Proof.ChaCha20.X86.Stream.within (below (VG.Proof.ChaCha20.X86.Stream.E s₀) 8) (by simp) 0 (by simp) (by simp)
    · exact VG.Proof.ChaCha20.X86.Stream.within (VG.Proof.ChaCha20.X86.Stream.stR s₀) (by simp) 64 rfl (by show 64 + 256 ≤ 768; omega)
  · rw [h.esp, h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Proof.ChaCha20.X86.Stream.within (VG.Proof.ChaCha20.X86.Stream.stR s₀) (by simp) 64 rfl (by show 64 + 256 ≤ 768; omega)

/-- A call returns in a state from which calls can be made, with the
callee-saved registers. -/
theorem At.ret {s₀ s s' : State} (h : VG.Proof.ChaCha20.X86.Stream.At s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) : VG.Proof.ChaCha20.X86.Stream.At s₀ s' :=
  ⟨by rw [cs .esp (by simp [calleeSaved]), h.esp], by rw [hrd, h.rd], by rw [hwr, h.wr]⟩

theorem block_call {s₀ s : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) (h : VG.Proof.ChaCha20.X86.Stream.At s₀ s) (hebx : s.gpr .ebx = ST s₀)
    (heax : s.gpr .eax = ST s₀ + BitVec.ofNat 32 64) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.ChaCha20.X86.Stream.At s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st s₀ + BitVec.ofNat 64 64, 256⟩, VG.Proof.ChaCha20.X86.Stream.stkR s₀] s.mem s'.mem →
      stateAt s'.mem (st s₀ + BitVec.ofNat 64 64) = block (stateAt s.mem (st s₀)) → Q s') :
    WP isa (callBlock) s Q := by
  have hk : [Reg.eax, .ebx].length ≤ 4 := by decide
  have fit := h.fit hp hk
  have e := hp.sp_lo
  refine WP.callWith Proof.ChaCha20.X86.block_correct VG.Proof.ChaCha20.X86.Stream.block_nosp (by simp) (by decide)
    (by rw [VG.Proof.ChaCha20.X86.Stream.block_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega)
    (VG.Proof.ChaCha20.X86.Stream.block_pre hp h hebx heax) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  rw [VG.Proof.ChaCha20.X86.Stream.block_stack, h.esp] at f'
  refine hQ s' (h.ret rd' wr' cs') cs' (f'.sub fun r hr => ?_) ?_
  · simp only [VG.Proof.ChaCha20.X86.Stream.wrBlk, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      List.length_cons, List.length_nil] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨VG.Proof.ChaCha20.X86.Stream.stkR s₀, by simp, below_sub (by omega) hp.sp_lo⟩
  · have a0 : arg (pushed [.eax, .ebx] s).callEntry 0 = ST s₀ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hebx
    have a1 : arg (pushed [.eax, .ebx] s).callEntry 1 = ST s₀ + BitVec.ofNat 32 64 := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact heax
    simp only [Proof.ChaCha20.blockX86, arg_withRegions, State.withRegions_mem, a0, a1,
      hp.eaS (d := 64) (by decide), m₂] at post
    rw [post, VG.Proof.ChaCha20.X86.Xor.stateAt_frame (h.entry_frame hp hk (by decide)) (by
      simp only [List.mem_singleton, forall_eq]
      exact (hp.stk_st.sub_right (VG.Proof.ChaCha20.X86.Stream.prefix_sub _ (by decide))).symm)]

/-! ## `vg_chacha20_xor` -/

/-- The regions of the call of `vg_chacha20_xor`: the copy of the state,
the data, the working space and its frame. -/
abbrev cpR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 192, 64⟩
abbrev blR (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.X86.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86.Stream.H s₀), 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀⟩
abbrev wkR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 256, 320⟩
abbrev wrXor (s₀ : State) : List Region := [VG.Proof.ChaCha20.X86.Stream.cpR s₀, VG.Proof.ChaCha20.X86.Stream.blR s₀, VG.Proof.ChaCha20.X86.Stream.wkR s₀, below (VG.Proof.ChaCha20.X86.Stream.E s₀) 16]

theorem cpR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.X86.Stream.cpR s₀) (VG.Proof.ChaCha20.X86.Stream.stR s₀) := Offset.sub_base _ (by omega)
theorem wkR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.X86.Stream.wkR s₀) (VG.Proof.ChaCha20.X86.Stream.stR s₀) := Offset.sub_base _ (by omega)
theorem blR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.X86.Stream.blR s₀) (VG.Proof.ChaCha20.X86.Stream.dR s₀) := Offset.sub_base _ (VG.Proof.ChaCha20.X86.Stream.HNB_le s₀)

theorem xor_pre {s₀ s : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) (h : VG.Proof.ChaCha20.X86.Stream.At s₀ s) (hnb : 0 < VG.Proof.ChaCha20.X86.Stream.NB s₀)
    (hedx : s.gpr .edx = ST s₀ + BitVec.ofNat 32 192) (hesi : s.gpr .esi = VG.Proof.ChaCha20.X86.Stream.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.H s₀))
    (hecx : s.gpr .ecx = BitVec.ofNat 32 (64 * VG.Proof.ChaCha20.X86.Stream.NB s₀)) (heax : s.gpr .eax = ST s₀ + BitVec.ofNat 32 256) :
    CallPre Proof.ChaCha20.xorX86 [.eax, .ecx, .esi, .edx] [] (VG.Proof.ChaCha20.X86.Stream.wrXor s₀) s := by
  have hk : [Reg.eax, .ecx, .esi, .edx].length ≤ 4 := by decide
  have fit := h.fit hp hk
  have hHNB := VG.Proof.ChaCha20.X86.Stream.HNB_le s₀
  have hL := VG.Proof.ChaCha20.X86.Stream.L_lt s₀
  have a0 : arg (pushed [.eax, .ecx, .esi, .edx] s).callEntry 0 = ST s₀ + BitVec.ofNat 32 192 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hedx
  have a1 : arg (pushed [.eax, .ecx, .esi, .edx] s).callEntry 1 = VG.Proof.ChaCha20.X86.Stream.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.H s₀) := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hesi
  have a2 : arg (pushed [.eax, .ecx, .esi, .edx] s).callEntry 2 = BitVec.ofNat 32 (64 * VG.Proof.ChaCha20.X86.Stream.NB s₀) := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hecx
  have a3 : arg (pushed [.eax, .ecx, .esi, .edx] s).callEntry 3 = ST s₀ + BitVec.ofNat 32 256 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact heax
  have e := hp.sp_lo
  have e₂ := hp.sp_hi
  have e' := hp.st_fit
  have ed := hp.d_fit
  have es : (VG.Proof.ChaCha20.X86.Stream.E s₀ - BitVec.ofNat 32 20).setWidth 64 - 12 = (VG.Proof.ChaCha20.X86.Stream.E s₀ - BitVec.ofNat 32 32).setWidth 64 := by
    rw [hp.E64 (by decide), hp.E64 (by decide), BitVec.sub_sub]; rfl
  have hn : (BitVec.ofNat 32 (64 * VG.Proof.ChaCha20.X86.Stream.NB s₀)).toNat = 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀ := Proof.ChaCha20.X86.Bytes.toNat_ofNat_lt32 (by omega)
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.ChaCha20.xorX86, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, h.argAddr0,
      h.esp64, h.espNat hp hk, hp.eaS (d := 192) (by decide), hp.eaS (d := 256) (by decide),
      hp.sNat (d := 192) (by decide), hp.sNat (d := 256) (by decide), hp.eaD (d := VG.Proof.ChaCha20.X86.Stream.H s₀) (by omega),
      hp.dNat (d := VG.Proof.ChaCha20.X86.Stream.H s₀) (by omega), hn, List.length_cons, List.length_nil, es]
    have sk : ∀ R, Region.Sub R (VG.Proof.ChaCha20.X86.Stream.stkR s₀) → ∀ R', Region.Sub R' (VG.Proof.ChaCha20.X86.Stream.stR s₀) → R.Disjoint R' :=
      fun R hR R' hR' => (hp.stk_st.sub_left hR).sub_right hR'
    have dk : ∀ R, Region.Sub R (VG.Proof.ChaCha20.X86.Stream.stkR s₀) → R.Disjoint (VG.Proof.ChaCha20.X86.Stream.blR s₀) :=
      fun R hR => (hp.stk_d.sub_left hR).sub_right (VG.Proof.ChaCha20.X86.Stream.blR_sub s₀)
    refine ⟨trivial, trivial, (hp.st_d.sub_left (VG.Proof.ChaCha20.X86.Stream.cpR_sub s₀)).sub_right (VG.Proof.ChaCha20.X86.Stream.blR_sub s₀),
      Offset.disjoint _ (by omega) (by omega) (by omega),
      (hp.st_d.sub_left (VG.Proof.ChaCha20.X86.Stream.wkR_sub s₀)).symm.sub_left (VG.Proof.ChaCha20.X86.Stream.blR_sub s₀),
      sk _ (hp.stk_part (by decide) (by decide)) _ (VG.Proof.ChaCha20.X86.Stream.cpR_sub s₀), dk _ (hp.stk_part (by decide) (by decide)),
      sk _ (hp.stk_part (by decide) (by decide)) _ (VG.Proof.ChaCha20.X86.Stream.wkR_sub s₀),
      sk _ (hp.stk_part (by decide) (by decide)) _ (VG.Proof.ChaCha20.X86.Stream.cpR_sub s₀), dk _ (hp.stk_part (by decide) (by decide)),
      sk _ (hp.stk_part (by decide) (by decide)) _ (VG.Proof.ChaCha20.X86.Stream.wkR_sub s₀),
      sk _ (hp.stk_part (by decide) (by decide)) _ (VG.Proof.ChaCha20.X86.Stream.cpR_sub s₀), dk _ (hp.stk_part (by decide) (by decide)),
      sk _ (hp.stk_part (by decide) (by decide)) _ (VG.Proof.ChaCha20.X86.Stream.wkR_sub s₀), by omega, by omega, by omega, by omega,
      by omega⟩
  · rw [h.esp, h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact VG.Proof.ChaCha20.X86.Stream.within (VG.Proof.ChaCha20.X86.Stream.stR s₀) (by simp) 192 rfl (by show 192 + 64 ≤ 768; omega)
    · exact VG.Proof.ChaCha20.X86.Stream.within (VG.Proof.ChaCha20.X86.Stream.dR s₀) (by simp) (VG.Proof.ChaCha20.X86.Stream.H s₀) rfl hHNB
    · exact VG.Proof.ChaCha20.X86.Stream.within (VG.Proof.ChaCha20.X86.Stream.stR s₀) (by simp) 256 rfl (by show 256 + 320 ≤ 768; omega)
    · exact VG.Proof.ChaCha20.X86.Stream.within (below (VG.Proof.ChaCha20.X86.Stream.E s₀) 16) (by simp) 0 (by simp) (by simp)
  · rw [h.esp, h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact VG.Proof.ChaCha20.X86.Stream.within (VG.Proof.ChaCha20.X86.Stream.stR s₀) (by simp) 192 rfl (by show 192 + 64 ≤ 768; omega)
    · exact VG.Proof.ChaCha20.X86.Stream.within (VG.Proof.ChaCha20.X86.Stream.dR s₀) (by simp) (VG.Proof.ChaCha20.X86.Stream.H s₀) rfl hHNB
    · exact VG.Proof.ChaCha20.X86.Stream.within (VG.Proof.ChaCha20.X86.Stream.stR s₀) (by simp) 256 rfl (by show 256 + 320 ≤ 768; omega)
    · exact VG.Proof.ChaCha20.X86.Stream.within (below (VG.Proof.ChaCha20.X86.Stream.E s₀) 16) (by simp) 0 (by simp) (by simp)

theorem xor_call (v : XorImpl) {s₀ s : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) (h : VG.Proof.ChaCha20.X86.Stream.At s₀ s) (hnb : 0 < VG.Proof.ChaCha20.X86.Stream.NB s₀)
    (hedx : s.gpr .edx = ST s₀ + BitVec.ofNat 32 192) (hesi : s.gpr .esi = VG.Proof.ChaCha20.X86.Stream.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.H s₀))
    (hecx : s.gpr .ecx = BitVec.ofNat 32 (64 * VG.Proof.ChaCha20.X86.Stream.NB s₀)) (heax : s.gpr .eax = ST s₀ + BitVec.ofNat 32 256)
    {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.ChaCha20.X86.Stream.At s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [VG.Proof.ChaCha20.X86.Stream.cpR s₀, VG.Proof.ChaCha20.X86.Stream.blR s₀, VG.Proof.ChaCha20.X86.Stream.wkR s₀, VG.Proof.ChaCha20.X86.Stream.stkR s₀] s.mem s'.mem →
      bytesAt s'.mem (VG.Proof.ChaCha20.X86.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86.Stream.H s₀)) (64 * VG.Proof.ChaCha20.X86.Stream.NB s₀) =
        List.zipWith (· ^^^ ·) (bytesAt s.mem (VG.Proof.ChaCha20.X86.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86.Stream.H s₀)) (64 * VG.Proof.ChaCha20.X86.Stream.NB s₀))
          (keystream (stateAt s.mem (st s₀ + BitVec.ofNat 64 192)) (64 * VG.Proof.ChaCha20.X86.Stream.NB s₀)) → Q s') :
    WP isa (callXor v.callee) s Q := by
  have hk : [Reg.eax, .ecx, .esi, .edx].length ≤ 4 := by decide
  have fit := h.fit hp hk
  have e := hp.sp_lo
  have hHNB := VG.Proof.ChaCha20.X86.Stream.HNB_le s₀
  have hL := VG.Proof.ChaCha20.X86.Stream.L_lt s₀
  refine WP.callWith v.ok v.nosp (by simp) (by decide)
    (by rw [v.stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega)
    (VG.Proof.ChaCha20.X86.Stream.xor_pre hp h hnb hedx hesi hecx heax) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  rw [v.stack, h.esp] at f'
  refine hQ s' (h.ret rd' wr' cs') cs' (f'.sub fun r hr => ?_) ?_
  · simp only [VG.Proof.ChaCha20.X86.Stream.wrXor, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      List.length_cons, List.length_nil] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨VG.Proof.ChaCha20.X86.Stream.stkR s₀, by simp, below_sub (by omega) hp.sp_lo⟩
    · exact ⟨VG.Proof.ChaCha20.X86.Stream.stkR s₀, by simp, below_sub (by omega) hp.sp_lo⟩
  · have a0 : arg (pushed [.eax, .ecx, .esi, .edx] s).callEntry 0 = ST s₀ + BitVec.ofNat 32 192 := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hedx
    have a1 : arg (pushed [.eax, .ecx, .esi, .edx] s).callEntry 1 = VG.Proof.ChaCha20.X86.Stream.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.H s₀) := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hesi
    have a2 : arg (pushed [.eax, .ecx, .esi, .edx] s).callEntry 2 = BitVec.ofNat 32 (64 * VG.Proof.ChaCha20.X86.Stream.NB s₀) := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hecx
    have hn : (BitVec.ofNat 32 (64 * VG.Proof.ChaCha20.X86.Stream.NB s₀)).toNat = 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀ :=
      Proof.ChaCha20.X86.Bytes.toNat_ofNat_lt32 (by omega)
    simp only [Proof.ChaCha20.xorX86, arg_withRegions, State.withRegions_mem, a0, a1, a2,
      hp.eaS (d := 192) (by decide), hp.eaD (d := VG.Proof.ChaCha20.X86.Stream.H s₀) (by omega), hn, m₂] at post
    have ef := h.entry_frame hp hk (by decide)
    rw [post, VG.Proof.ChaCha20.X86.Stream.bytesAt_frame ef (by
      simp only [List.mem_singleton, forall_eq]; exact (hp.stk_d.sub_right (VG.Proof.ChaCha20.X86.Stream.blR_sub s₀)).symm) (by omega),
      VG.Proof.ChaCha20.X86.Xor.stateAt_frame ef (by
        simp only [List.mem_singleton, forall_eq]; exact (hp.stk_st.sub_right (VG.Proof.ChaCha20.X86.Stream.cpR_sub s₀)).symm)]

end VG.Proof.ChaCha20.X86.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.X86.Stream.Apply`. -/
section

/-!
# Streaming ChaCha20 on x86 (32-bit): `apply`, correctness

Untrusted: everything here is checked by Lean. The pieces of `apply`
(`Impl/ChaCha20/X86/Stream.lean`), each from what holds before it
(`Q0` … `Q3`), and the whole function. The pieces are those that the proof
of constant time (`ApplyCT.lean`) relates in two runs.
-/

namespace VG.Proof.ChaCha20.X86.Stream

open VG VG.X86 VG.Impl.ChaCha20.X86.Stream
open VG.Impl.ChaCha20.X86 (at_)
open VG.Impl.ChaCha20.X86.Xor (xorBytes)
open VG.Proof.ChaCha20.X86 (contains_off XorImpl)
open VG.Proof.ChaCha20.X86.Bytes (toNat_ofNat_lt32 ptr_add BPre BPost xorBytes_ok ofNat32_beq_zero)
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt stateAt serialize block)

/-! ## The check -/

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) :
    WP isa (.block [.mov .eax (.mem (at_ .esp 4))]) s₀ fun s => s = s₀.setReg .eax (ST s₀) := by
  have i₀ : InRegions (s₀.rd ++ s₀.wr) ((s₀.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 4 := hp.in_arg (i := 0) (by decide)
  have v₀ : s₀.mem.readW ((s₀.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 32 = ST s₀ := rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.ea, at_, State.load32,
    i₀, v₀, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']

/-- After the check: `edx:ecx` holds the bytes left less `len` (modulo
2⁶⁴), and the borrow whether fewer than `len` are left. -/
structure Q0 (s₀ s : State) : Prop where
  eax : s.gpr .eax = ST s₀
  pair : Pair s ((VG.Proof.ChaCha20.X86.Stream.N s₀ + 2 ^ 64 - VG.Proof.ChaCha20.X86.Stream.L s₀) % 2 ^ 64)
  cf : s.cf = some (decide (VG.Proof.ChaCha20.X86.Stream.N s₀ < VG.Proof.ChaCha20.X86.Stream.L s₀))
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

set_option simprocs false in
theorem check_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) : WP isa (.block check) (s₀.setReg .eax (ST s₀)) (VG.Proof.ChaCha20.X86.Stream.Q0 s₀) := by
  have i₂ : InRegions (s₀.rd ++ s₀.wr) ((s₀.gpr .esp + BitVec.ofNat 32 12).setWidth 64) 4 := hp.in_arg (i := 2) (by decide)
  have v₂ : s₀.mem.readW ((s₀.gpr .esp + BitVec.ofNat 32 12).setWidth 64) 32 = VG.Proof.ChaCha20.X86.Stream.LN s₀ := rfl
  have e₁ := hp.eaS (d := 128) (by decide); have e₂ := hp.eaS (d := 132) (by decide)
  have j₁ := hp.r_st (d := 128) (n := 4) (by decide); have j₂ := hp.r_st (d := 132) (n := 4) (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [check, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.ea, at_, State.load32, execAlu, arithFlags, State.setReg, State.setFlags, i₂, v₂, e₁, e₂, j₁, j₂,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hN : VG.Proof.ChaCha20.X86.Stream.N s₀ = (s₀.mem.readW (st s₀ + BitVec.ofNat 64 128) 32).toNat +
      2 ^ 32 * (s₀.mem.readW (st s₀ + BitVec.ofNat 64 132) 32).toNat := by
    simp only [VG.Proof.ChaCha20.X86.Stream.N, leftAt]
    rw [show (st s₀ + 128 : Addr) = st s₀ + BitVec.ofNat 64 128 from rfl, readW64_toNat, Offset.add_add]
  have hL : VG.Proof.ChaCha20.X86.Stream.L s₀ = (VG.Proof.ChaCha20.X86.Stream.LN s₀).toNat := rfl
  refine ⟨by simp (config := {decide := true}), ?_, ?_, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃], rfl, rfl, rfl⟩
  all_goals simp (config := {decide := true}) only [Pair, ite_true, ite_false]
  all_goals
    have ha := (s₀.mem.readW (st s₀ + BitVec.ofNat 64 128) 32).isLt
    have hb := (s₀.mem.readW (st s₀ + BitVec.ofNat 64 132) 32).isLt
    have hl := (VG.Proof.ChaCha20.X86.Stream.LN s₀).isLt
    rw [hN, hL]
    generalize s₀.mem.readW (st s₀ + BitVec.ofNat 64 128) 32 = a at *
    generalize s₀.mem.readW (st s₀ + BitVec.ofNat 64 132) 32 = b at *
    generalize VG.Proof.ChaCha20.X86.Stream.LN s₀ = l at *
  · rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
    by_cases hc : a.toNat < l.toNat
    · simp only [hc, decide_true, Bool.toNat_true]; simp; omega
    · simp only [hc, decide_false, Bool.toNat_false]; simp; omega
  · congr 1
    by_cases hc : a.toNat < l.toNat
    · simp only [hc, decide_true, Bool.toNat_true]; simp; omega
    · simp only [hc, decide_false, Bool.toNat_false]; simp; omega

/-- What `apply` guarantees (`applyX86`), and the registers it keeps. -/
def Final (s₀ s : State) : Prop := abiPreserved s₀ s ∧ Proof.ChaCha20.applyX86.post s₀ s

set_option simprocs false in
theorem fail_ok {s₀ : State} (hlt : VG.Proof.ChaCha20.X86.Stream.N s₀ < VG.Proof.ChaCha20.X86.Stream.L s₀) {s : State} (h : VG.Proof.ChaCha20.X86.Stream.Q0 s₀ s) :
    WP isa (.block [.mov .eax (.imm 0)]) s (VG.Proof.ChaCha20.X86.Stream.Final s₀) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨⟨fun r hr => ?_, by rw [RegUpd.mem_setReg, h.mem]⟩, ?_⟩
  · rw [RegUpd.gpr_setReg_of_ne _ _ (calleeSaved_ne hr).1]
    exact h.keep r (calleeSaved_ne hr).1 (calleeSaved_ne hr).2.1 (calleeSaved_ne hr).2.2
  · show keyAt _ _ = _ ∧ _
    rw [ite_neg (show ¬ VG.Proof.ChaCha20.X86.Stream.L s₀ ≤ VG.Proof.ChaCha20.X86.Stream.N s₀ by omega)]
    rw [RegUpd.mem_setReg, h.mem]
    exact ⟨rfl, RegUpd.gpr_setReg_self .., rfl, rfl⟩

/-! ## The bytes left in the buffered block -/

/-- `and` with `0xffffffc0` rounds down to a multiple of 64. -/
theorem and_mask (x : BitVec 32) : x &&& (0xffffffc0 : BitVec 32) = BitVec.ofNat 32 (x.toNat / 64 * 64) := by
  have : (0xffffffc0 : BitVec 32) = BitVec.ofNat 32 ((2 ^ 26 - 1) <<< 6) := by decide
  rw [this]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hx := x.isLt
  generalize x.toNat = n at *
  rw [Nat.mod_eq_of_lt (by decide), Nat.mod_eq_of_lt (by omega),
    show n / 64 * 64 = (n >>> 6) <<< 6 by rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : 6 ≤ i
  · by_cases h2 : i - 6 < 26
    · simp [hi, h2, show 6 + (i - 6) = i by omega]
    · have : n.testBit i = false := Nat.testBit_lt_two_pow (by
        calc n < 2 ^ 32 := hx
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [hi, h2, this, show 6 + (i - 6) = i by omega]
  · simp [hi]

/-- `and` with 63: the remainder modulo 64. -/
theorem and_63 (x : BitVec 32) : x &&& (63 : BitVec 32) = BitVec.ofNat 32 (x.toNat % 64) := by
  have : (63 : BitVec 32) = BitVec.ofNat 32 (2 ^ 6 - 1) := by decide
  rw [this]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 ^ 6 - 1 < 2 ^ 32 by decide), Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- Our caller's `ebx, esi, edi, ebp`, and the bytes left after `apply`. -/
structure Saved (s₀ : State) (m : Mem) : Prop where
  ebx : m.readW (st s₀ + BitVec.ofNat 64 576) 32 = s₀.gpr .ebx
  esi : m.readW (st s₀ + BitVec.ofNat 64 580) 32 = s₀.gpr .esi
  edi : m.readW (st s₀ + BitVec.ofNat 64 584) 32 = s₀.gpr .edi
  ebp : m.readW (st s₀ + BitVec.ofNat 64 588) 32 = s₀.gpr .ebp
  lo : m.readW (st s₀ + BitVec.ofNat 64 600) 32 = BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.N s₀ - VG.Proof.ChaCha20.X86.Stream.L s₀)
  hi : m.readW (st s₀ + BitVec.ofNat 64 604) 32 = BitVec.ofNat 32 ((VG.Proof.ChaCha20.X86.Stream.N s₀ - VG.Proof.ChaCha20.X86.Stream.L s₀) / 2 ^ 32)

/-- Where they are. -/
abbrev savR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 576, 32⟩

theorem savR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.X86.Stream.savR s₀) (VG.Proof.ChaCha20.X86.Stream.stR s₀) := Offset.sub_base _ (by omega)

theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : VG.Proof.ChaCha20.X86.Stream.Saved s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (VG.Proof.ChaCha20.X86.Stream.savR s₀).Disjoint r) : VG.Proof.ChaCha20.X86.Stream.Saved s₀ m' := by
  have c : ∀ d, 576 ≤ d → d + 4 ≤ 608 → (VG.Proof.ChaCha20.X86.Stream.savR s₀).Contains (st s₀ + BitVec.ofNat 64 d) (32 / 8) :=
    fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
  exact ⟨by rw [hf.readW (c 576 (by decide) (by decide)) hd (by decide), h.ebx],
    by rw [hf.readW (c 580 (by decide) (by decide)) hd (by decide), h.esi],
    by rw [hf.readW (c 584 (by decide) (by decide)) hd (by decide), h.edi],
    by rw [hf.readW (c 588 (by decide) (by decide)) hd (by decide), h.ebp],
    by rw [hf.readW (c 600 (by decide) (by decide)) hd (by decide), h.lo],
    by rw [hf.readW (c 604 (by decide) (by decide)) hd (by decide), h.hi]⟩

/-- The state of memory before the data is touched. -/
structure Mid (s₀ : State) (m : Mem) : Prop where
  keep : ∀ i < 136, m (st s₀ + BitVec.ofNat 64 i) = s₀.mem (st s₀ + BitVec.ofNat 64 i)
  saved : VG.Proof.ChaCha20.X86.Stream.Saved s₀ m

theorem Mid.state {s₀ : State} {m : Mem} (h : VG.Proof.ChaCha20.X86.Stream.Mid s₀ m) : stateAt m (st s₀) = VG.Proof.ChaCha20.X86.Stream.S0 s₀ :=
  stateAt_congr fun i hi => h.keep i (by omega)

/-- The memory after `start`'s stores. -/
def startMem (m : Mem) (st : Addr) (b si di bp lo hi : BitVec 32) : Mem :=
  (((((m.writeW (st + BitVec.ofNat 64 576) b).writeW (st + BitVec.ofNat 64 580) si).writeW
    (st + BitVec.ofNat 64 584) di).writeW (st + BitVec.ofNat 64 588) bp).writeW (st + BitVec.ofNat 64 600) lo).writeW
    (st + BitVec.ofNat 64 604) hi

theorem startMem_frame (m : Mem) (st : Addr) (b si di bp lo hi : BitVec 32) :
    Frame [⟨st, 768⟩] m (VG.Proof.ChaCha20.X86.Stream.startMem m st b si di bp lo hi) := by
  have c : ∀ d, d + 4 ≤ 768 → (⟨st, 768⟩ : Region).Contains (st + BitVec.ofNat 64 d) (32 / 8) :=
    fun d hd => contains_off hd (by omega)
  exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 576 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 580 (by decide))).writeW (List.mem_singleton_self _) _
    (c 584 (by decide))).writeW (List.mem_singleton_self _) _ (c 588 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 600 (by decide))).writeW (List.mem_singleton_self _) _ (c 604 (by decide))

set_option simprocs false in
theorem startMem_read (m : Mem) (st : Addr) (b si di bp lo hi : BitVec 32) {d : Nat} (hd : d + 4 ≤ 576) :
    (VG.Proof.ChaCha20.X86.Stream.startMem m st b si di bp lo hi).readW (st + BitVec.ofNat 64 d) 32 = m.readW (st + BitVec.ofNat 64 d) 32 := by
  simp only [VG.Proof.ChaCha20.X86.Stream.startMem]
  rw [readW_ofNat32 _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_ofNat32 _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_ofNat32 _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_ofNat32 _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_ofNat32 _ _ _ (by omega) (by omega) (by omega) (by omega),
    readW_ofNat32 _ _ _ (by omega) (by omega) (by omega) (by omega)]

theorem startMem_byte (m : Mem) (st : Addr) (b si di bp lo hi : BitVec 32) {i : Nat} (hi' : i < 576) :
    (VG.Proof.ChaCha20.X86.Stream.startMem m st b si di bp lo hi) (st + BitVec.ofNat 64 i) = m (st + BitVec.ofNat 64 i) := by
  simp only [VG.Proof.ChaCha20.X86.Stream.startMem]
  rw [byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
    byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
    byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)]

set_option simprocs false in
theorem startMem_saved (s₀ : State) :
    VG.Proof.ChaCha20.X86.Stream.Saved s₀ (VG.Proof.ChaCha20.X86.Stream.startMem s₀.mem (st s₀) (s₀.gpr .ebx) (s₀.gpr .esi) (s₀.gpr .edi) (s₀.gpr .ebp)
      (BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.N s₀ - VG.Proof.ChaCha20.X86.Stream.L s₀)) (BitVec.ofNat 32 ((VG.Proof.ChaCha20.X86.Stream.N s₀ - VG.Proof.ChaCha20.X86.Stream.L s₀) / 2 ^ 32))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp (config := {decide := true}) only [VG.Proof.ChaCha20.X86.Stream.startMem, Mem.readW_writeW_self32, readW_ofNat32]

def startStores : List Instr :=
  [.store (at_ .eax 576) .ebx, .store (at_ .eax 580) .esi, .store (at_ .eax 584) .edi,
   .store (at_ .eax 588) .ebp, .store (at_ .eax 600) .ecx, .store (at_ .eax 604) .edx]

def startLoads : List Instr :=
  [.mov .ebx (.reg .eax), .mov .esi (.mem (at_ .esp 8)), .mov .ebp (.mem (at_ .esp 12)),
   .mov .eax (.mem (at_ .ebx 128)), .alu .and .eax (.imm 63), .mov .ecx (.reg .ebp),
   .alu .cmp .eax (.reg .ebp)]

theorem start_eq : start = VG.Proof.ChaCha20.X86.Stream.startStores ++ VG.Proof.ChaCha20.X86.Stream.startLoads := rfl

/-- After `start`, with `x` in `ecx`. -/
structure R1 (s₀ : State) (x : Nat) (s : State) : Prop where
  ebx : s.gpr .ebx = ST s₀
  esi : s.gpr .esi = VG.Proof.ChaCha20.X86.Stream.DP s₀
  ebp : s.gpr .ebp = VG.Proof.ChaCha20.X86.Stream.LN s₀
  ecx : s.gpr .ecx = BitVec.ofNat 32 x
  eax : s.gpr .eax = BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.O s₀)
  esp : s.gpr .esp = VG.Proof.ChaCha20.X86.Stream.E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mid : VG.Proof.ChaCha20.X86.Stream.Mid s₀ s.mem
  done : VG.Proof.ChaCha20.X86.Stream.Done s₀ 0 s.mem
  frame : Frame [VG.Proof.ChaCha20.X86.Stream.stR s₀] s₀.mem s.mem

set_option simprocs false in
theorem startStores_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) (hle : VG.Proof.ChaCha20.X86.Stream.L s₀ ≤ VG.Proof.ChaCha20.X86.Stream.N s₀) {s : State} (h : VG.Proof.ChaCha20.X86.Stream.Q0 s₀ s) :
    WP isa (.block VG.Proof.ChaCha20.X86.Stream.startStores) s fun s' => s'.gpr = s.gpr ∧
      s'.mem = VG.Proof.ChaCha20.X86.Stream.startMem s₀.mem (st s₀) (s₀.gpr .ebx) (s₀.gpr .esi) (s₀.gpr .edi) (s₀.gpr .ebp)
        (BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.N s₀ - VG.Proof.ChaCha20.X86.Stream.L s₀)) (BitVec.ofNat 32 ((VG.Proof.ChaCha20.X86.Stream.N s₀ - VG.Proof.ChaCha20.X86.Stream.L s₀) / 2 ^ 32)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ⟨hecx, hedx⟩ := pair_eq h.pair (by omega)
  rw [show (VG.Proof.ChaCha20.X86.Stream.N s₀ + 2 ^ 64 - VG.Proof.ChaCha20.X86.Stream.L s₀) % 2 ^ 64 = VG.Proof.ChaCha20.X86.Stream.N s₀ - VG.Proof.ChaCha20.X86.Stream.L s₀ by have := VG.Proof.ChaCha20.X86.Stream.N_lt s₀; omega] at hecx hedx
  have e : ∀ d, d < 768 → (s.gpr .eax + BitVec.ofNat 32 d).setWidth 64 = st s₀ + BitVec.ofNat 64 d :=
    fun d hd => by rw [h.eax]; exact hp.eaS hd
  have o : ∀ d, d + 4 ≤ 768 → InRegions s.wr (st s₀ + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [h.wr]; exact hp.w_st hd
  have e576 := e 576 (by decide); have e580 := e 580 (by decide); have e584 := e 584 (by decide)
  have e588 := e 588 (by decide); have e600 := e 600 (by decide); have e604 := e 604 (by decide)
  have o576 := o 576 (by decide); have o580 := o 580 (by decide); have o584 := o 584 (by decide)
  have o588 := o 588 (by decide); have o600 := o 600 (by decide); have o604 := o 604 (by decide)
  have kb := h.keep .ebx (by decide) (by decide) (by decide)
  have ks := h.keep .esi (by decide) (by decide) (by decide)
  have kd := h.keep .edi (by decide) (by decide) (by decide)
  have kp := h.keep .ebp (by decide) (by decide) (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [VG.Proof.ChaCha20.X86.Stream.startStores, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.ea, at_, State.store32, e576, e580, e584, e588, e600, e604, o576, o580, o584, o588, o600, o604,
    kb, ks, kd, kp, hecx, hedx, h.mem, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, trivial⟩

theorem lo_mod (s₀ : State) : (s₀.mem.readW (st s₀ + BitVec.ofNat 64 128) 32).toNat % 64 = VG.Proof.ChaCha20.X86.Stream.O s₀ := by
  simp only [VG.Proof.ChaCha20.X86.Stream.O, VG.Proof.ChaCha20.X86.Stream.N, leftAt]
  rw [show (st s₀ + 128 : Addr) = st s₀ + BitVec.ofNat 64 128 from rfl, readW64_toNat]
  omega

set_option simprocs false in
theorem startLoads_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.X86.Stream.Q0 s₀ s) {s₁ : State} (g₁ : s₁.gpr = s.gpr)
    (m₁ : s₁.mem = VG.Proof.ChaCha20.X86.Stream.startMem s₀.mem (st s₀) (s₀.gpr .ebx) (s₀.gpr .esi) (s₀.gpr .edi) (s₀.gpr .ebp)
        (BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.N s₀ - VG.Proof.ChaCha20.X86.Stream.L s₀)) (BitVec.ofNat 32 ((VG.Proof.ChaCha20.X86.Stream.N s₀ - VG.Proof.ChaCha20.X86.Stream.L s₀) / 2 ^ 32)))
    (r₁ : s₁.rd = s.rd) (w₁ : s₁.wr = s.wr) :
    WP isa (.block VG.Proof.ChaCha20.X86.Stream.startLoads) s₁ fun s' => VG.Proof.ChaCha20.X86.Stream.R1 s₀ (VG.Proof.ChaCha20.X86.Stream.L s₀) s' ∧ s'.cf = some (decide (VG.Proof.ChaCha20.X86.Stream.O s₀ < VG.Proof.ChaCha20.X86.Stream.L s₀)) := by
  have hf := VG.Proof.ChaCha20.X86.Stream.startMem_frame s₀.mem (st s₀) (s₀.gpr .ebx) (s₀.gpr .esi) (s₀.gpr .edi) (s₀.gpr .ebp)
    (BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.N s₀ - VG.Proof.ChaCha20.X86.Stream.L s₀)) (BitVec.ofNat 32 ((VG.Proof.ChaCha20.X86.Stream.N s₀ - VG.Proof.ChaCha20.X86.Stream.L s₀) / 2 ^ 32))
  have ha : ∀ i, i < 3 → (VG.Proof.ChaCha20.X86.Stream.startMem s₀.mem (st s₀) (s₀.gpr .ebx) (s₀.gpr .esi) (s₀.gpr .edi) (s₀.gpr .ebp)
      (BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.N s₀ - VG.Proof.ChaCha20.X86.Stream.L s₀)) (BitVec.ofNat 32 ((VG.Proof.ChaCha20.X86.Stream.N s₀ - VG.Proof.ChaCha20.X86.Stream.L s₀) / 2 ^ 32))).readW (argAddr s₀ i) 32 =
      arg s₀ i := fun i hi =>
    hf.readW (arg_in s₀ (n := 3) (by have := hp.sp_hi; omega) hi) (by simpa using hp.a_st) (by decide)
  have gesp : s₁.gpr .esp = VG.Proof.ChaCha20.X86.Stream.E s₀ := by rw [g₁, h.keep .esp (by decide) (by decide) (by decide)]
  have geax : s₁.gpr .eax = ST s₀ := by rw [g₁, h.eax]
  have i₁ : InRegions (s₁.rd ++ s₁.wr) ((VG.Proof.ChaCha20.X86.Stream.E s₀ + BitVec.ofNat 32 8).setWidth 64) 4 := by
    rw [r₁, w₁, h.rd, h.wr]; exact hp.in_arg (i := 1) (by decide)
  have i₂ : InRegions (s₁.rd ++ s₁.wr) ((VG.Proof.ChaCha20.X86.Stream.E s₀ + BitVec.ofNat 32 12).setWidth 64) 4 := by
    rw [r₁, w₁, h.rd, h.wr]; exact hp.in_arg (i := 2) (by decide)
  have v₁ := ha 1 (by decide)
  have v₂ := ha 2 (by decide)
  have e₃ := hp.eaS (d := 128) (by decide)
  have i₃ : InRegions (s₁.rd ++ s₁.wr) (st s₀ + BitVec.ofNat 64 128) 4 := by
    rw [r₁, w₁, h.rd, h.wr]; exact hp.r_st (by decide)
  have v₃ := VG.Proof.ChaCha20.X86.Stream.startMem_read s₀.mem (st s₀) (s₀.gpr .ebx) (s₀.gpr .esi) (s₀.gpr .edi) (s₀.gpr .ebp)
    (BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.N s₀ - VG.Proof.ChaCha20.X86.Stream.L s₀)) (BitVec.ofNat 32 ((VG.Proof.ChaCha20.X86.Stream.N s₀ - VG.Proof.ChaCha20.X86.Stream.L s₀) / 2 ^ 32)) (d := 128) (by decide)
  simp only [argAddr] at v₁ v₂
  apply WP.of_runBlock
  simp (config := {decide := true}) only [VG.Proof.ChaCha20.X86.Stream.startLoads, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.ea, at_, State.load32, execAlu, arithFlags, State.setReg, State.setFlags, gesp, geax, m₁, i₁, i₂, i₃,
    v₁, v₂, e₃, v₃, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    VG.Proof.ChaCha20.X86.Stream.and_63, VG.Proof.ChaCha20.X86.Stream.lo_mod]
  have hO : VG.Proof.ChaCha20.X86.Stream.O s₀ < 2 ^ 32 := by have := VG.Proof.ChaCha20.X86.Stream.O_lt s₀; omega
  refine ⟨⟨by simp (config := {decide := true}), by simp (config := {decide := true}),
    by simp (config := {decide := true}), by simp (config := {decide := true}) [VG.Proof.ChaCha20.X86.Stream.L],
    by simp (config := {decide := true}), by simp (config := {decide := true}) [gesp], by rw [r₁, h.rd],
    by rw [w₁, h.wr], ⟨fun i hi => VG.Proof.ChaCha20.X86.Stream.startMem_byte _ _ _ _ _ _ _ _ (by omega), VG.Proof.ChaCha20.X86.Stream.startMem_saved s₀⟩,
    fun k hk => ?_, hf⟩, ?_⟩
  · dsimp only
    rw [hf.bytes (R := VG.Proof.ChaCha20.X86.Stream.dR s₀) (by simpa using hp.st_d.symm) (show VG.Proof.ChaCha20.X86.Stream.L s₀ ≤ 2 ^ 64 by have := VG.Proof.ChaCha20.X86.Stream.L_lt s₀; omega) hk]
    simp
  · simp only [Proof.ChaCha20.X86.Bytes.toNat_ofNat_lt32 hO]

theorem start_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) (hle : VG.Proof.ChaCha20.X86.Stream.L s₀ ≤ VG.Proof.ChaCha20.X86.Stream.N s₀) {s : State} (h : VG.Proof.ChaCha20.X86.Stream.Q0 s₀ s) :
    WP isa (.block start) s fun s' => VG.Proof.ChaCha20.X86.Stream.R1 s₀ (VG.Proof.ChaCha20.X86.Stream.L s₀) s' ∧ s'.cf = some (decide (VG.Proof.ChaCha20.X86.Stream.O s₀ < VG.Proof.ChaCha20.X86.Stream.L s₀)) := by
  rw [VG.Proof.ChaCha20.X86.Stream.start_eq, WP.block_append_iff]
  exact WP.mono (VG.Proof.ChaCha20.X86.Stream.startStores_ok hp hle h) fun s₁ ⟨g₁, m₁, r₁, w₁⟩ => VG.Proof.ChaCha20.X86.Stream.startLoads_ok hp h g₁ m₁ r₁ w₁

set_option simprocs false in
theorem sel_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20.X86.Stream.R1 s₀ (VG.Proof.ChaCha20.X86.Stream.L s₀) s) (hc : s.cf = some (decide (VG.Proof.ChaCha20.X86.Stream.O s₀ < VG.Proof.ChaCha20.X86.Stream.L s₀))) :
    WP isa (.ite .b (.block [.mov .ecx (.reg .eax)]) (.block [])) s (VG.Proof.ChaCha20.X86.Stream.R1 s₀ (VG.Proof.ChaCha20.X86.Stream.H s₀)) := by
  refine WP.ite (decide (VG.Proof.ChaCha20.X86.Stream.O s₀ < VG.Proof.ChaCha20.X86.Stream.L s₀)) (by show eval .b s = _; simp only [eval, hc]) (fun hlt => ?_) (fun hge => ?_)
  · simp only [decide_eq_true_eq] at hlt
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
      Option.some.injEq, exists_eq_left']
    have g : ∀ r, r ≠ .ecx → (s.setReg .ecx (s.gpr .eax)).gpr r = s.gpr r := fun r hr =>
      RegUpd.gpr_setReg_of_ne _ _ hr
    exact ⟨by rw [g _ (by decide), h.ebx], by rw [g _ (by decide), h.esi], by rw [g _ (by decide), h.ebp],
      by rw [RegUpd.gpr_setReg_self, h.eax, VG.Proof.ChaCha20.X86.Stream.H, headLen, bufLeft, Nat.min_eq_left (Nat.le_of_lt hlt)],
      by rw [g _ (by decide), h.eax], by rw [g _ (by decide), h.esp], h.rd, h.wr, h.mid, h.done, h.frame⟩
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
    refine WP.block_nil (M := isa) ⟨h.ebx, h.esi, h.ebp, ?_, h.eax, h.esp, h.rd, h.wr, h.mid, h.done, h.frame⟩
    rw [h.ecx, VG.Proof.ChaCha20.X86.Stream.H, headLen, bufLeft, Nat.min_eq_right hge]

theorem sub_ofNat32 {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- After the pointer to the bytes left in the buffered block is computed. -/
structure R2 (s₀ s : State) : Prop where
  ebx : s.gpr .ebx = ST s₀
  esi : s.gpr .esi = VG.Proof.ChaCha20.X86.Stream.DP s₀
  ebp : s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.L s₀ - VG.Proof.ChaCha20.X86.Stream.H s₀)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.H s₀)
  edx : s.gpr .edx = ST s₀ + BitVec.ofNat 32 (128 - VG.Proof.ChaCha20.X86.Stream.O s₀)
  esp : s.gpr .esp = VG.Proof.ChaCha20.X86.Stream.E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mid : VG.Proof.ChaCha20.X86.Stream.Mid s₀ s.mem
  done : VG.Proof.ChaCha20.X86.Stream.Done s₀ 0 s.mem
  frame : Frame [VG.Proof.ChaCha20.X86.Stream.stR s₀] s₀.mem s.mem

set_option simprocs false in
theorem ptr_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20.X86.Stream.R1 s₀ (VG.Proof.ChaCha20.X86.Stream.H s₀) s) :
    WP isa (.block (ptr .edx .ebx 128 ++ ([.alu .sub .edx (.reg .eax), .alu .sub .ebp (.reg .ecx)] : List Instr))) s (VG.Proof.ChaCha20.X86.Stream.R2 s₀) := by
  have hO := VG.Proof.ChaCha20.X86.Stream.O_lt s₀
  have hH := VG.Proof.ChaCha20.X86.Stream.H_le s₀
  have hL := VG.Proof.ChaCha20.X86.Stream.L_lt s₀
  apply WP.of_runBlock
  simp (config := {decide := true}) only [ptr, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', ite_true, ite_false]
  refine ⟨by simp (config := {decide := true}) [h.ebx], by simp (config := {decide := true}) [h.esi], ?_,
    by simp (config := {decide := true}) [h.ecx], ?_, by simp (config := {decide := true}) [h.esp], h.rd, h.wr,
    h.mid, h.done, h.frame⟩
  · simp (config := {decide := true}) only [ite_true, ite_false, h.ebp, h.ecx]
    rw [show VG.Proof.ChaCha20.X86.Stream.LN s₀ = BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.L s₀) by simp [VG.Proof.ChaCha20.X86.Stream.L], VG.Proof.ChaCha20.X86.Stream.sub_ofNat32 hH]
  · simp (config := {decide := true}) only [ite_true, ite_false, h.ebx, h.eax]
    rw [show (128#32 : BitVec 32) = BitVec.ofNat 32 (128 - VG.Proof.ChaCha20.X86.Stream.O s₀) + BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.O s₀) by
        rw [BitVec.ofNat_add_ofNat, show 128 - VG.Proof.ChaCha20.X86.Stream.O s₀ + VG.Proof.ChaCha20.X86.Stream.O s₀ = 128 by omega],
      ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- After `part1`: the bytes from the buffered block XORed, and `ecx` the
bytes of the whole blocks. -/
structure Q1 (s₀ s : State) : Prop where
  ebx : s.gpr .ebx = ST s₀
  esi : s.gpr .esi = VG.Proof.ChaCha20.X86.Stream.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.H s₀)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.L s₀ - VG.Proof.ChaCha20.X86.Stream.H s₀)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (64 * VG.Proof.ChaCha20.X86.Stream.NB s₀)
  zf : s.zf = some (decide (64 * VG.Proof.ChaCha20.X86.Stream.NB s₀ = 0))
  esp : s.gpr .esp = VG.Proof.ChaCha20.X86.Stream.E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mid : VG.Proof.ChaCha20.X86.Stream.Mid s₀ s.mem
  done : VG.Proof.ChaCha20.X86.Stream.Done s₀ (VG.Proof.ChaCha20.X86.Stream.H s₀) s.mem
  frame : Frame [VG.Proof.ChaCha20.X86.Stream.stR s₀, VG.Proof.ChaCha20.X86.Stream.dR s₀] s₀.mem s.mem

theorem part1_eq : part1 = .seq (.block start)
    (.seq (.ite .b (.block [.mov .ecx (.reg .eax)]) (.block []))
    (.seq (.block (ptr .edx .ebx 128 ++ ([.alu .sub .edx (.reg .eax), .alu .sub .ebp (.reg .ecx)] : List Instr)))
    (.seq xorBytes (.block [.mov .ecx (.reg .ebp), .alu .and .ecx (.imm 0xffffffc0)])))) := rfl

/-- The rest of `part1`, after the selection. -/
abbrev rest1 : Prog isa :=
  .seq (.block (ptr .edx .ebx 128 ++ ([.alu .sub .edx (.reg .eax), .alu .sub .ebp (.reg .ecx)] : List Instr)))
    (.seq xorBytes (.block [.mov .ecx (.reg .ebp), .alu .and .ecx (.imm 0xffffffc0)]))

set_option simprocs false in
theorem rest1_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) {s₂ : State} (h₂ : VG.Proof.ChaCha20.X86.Stream.R1 s₀ (VG.Proof.ChaCha20.X86.Stream.H s₀) s₂) :
    WP isa VG.Proof.ChaCha20.X86.Stream.rest1 s₂ (VG.Proof.ChaCha20.X86.Stream.Q1 s₀) := by
  have hL := VG.Proof.ChaCha20.X86.Stream.L_lt s₀
  have hH := VG.Proof.ChaCha20.X86.Stream.H_le s₀
  have hHO := VG.Proof.ChaCha20.X86.Stream.H_le_O s₀
  have hO := VG.Proof.ChaCha20.X86.Stream.O_lt s₀
  have hst := hp.st_fit
  have hd := hp.d_fit
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Stream.ptr_ok h₂) fun s₃ h₃ => ?_)
  have eK : (ST s₀ + BitVec.ofNat 32 (128 - VG.Proof.ChaCha20.X86.Stream.O s₀)).setWidth 64 = st s₀ + BitVec.ofNat 64 (128 - VG.Proof.ChaCha20.X86.Stream.O s₀) :=
    hp.eaS (by omega)
  have hb : BPre s₃ (VG.Proof.ChaCha20.X86.Stream.DP s₀) (ST s₀ + BitVec.ofNat 32 (128 - VG.Proof.ChaCha20.X86.Stream.O s₀)) (VG.Proof.ChaCha20.X86.Stream.H s₀) :=
    ⟨h₃.esi, h₃.edx, h₃.ecx, by omega, by rw [hp.sNat (by omega)]; omega,
      fun k hk => ⟨VG.Proof.ChaCha20.X86.Stream.dR s₀, by rw [h₃.wr, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun k hk => by rw [h₃.rd, h₃.wr, eK, Offset.add_add]; exact hp.r_st (by omega),
      fun j hj k hk => by rw [eK, Offset.add_add]; exact VG.Proof.ChaCha20.X86.Stream.d_ne_st hp (by omega) (by omega)⟩
  refine WP.seq (WP.mono (xorBytes_ok hb) fun s₄ h₄ => ?_)
  have hebp : s₄.gpr .ebp = BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.L s₀ - VG.Proof.ChaCha20.X86.Stream.H s₀) := by
    rw [h₄.keep _ (by decide) (by decide) (by decide) (by decide), h₃.ebp]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, hebp, VG.Proof.ChaCha20.X86.Stream.and_mask,
    Proof.ChaCha20.X86.Bytes.toNat_ofNat_lt32 (show VG.Proof.ChaCha20.X86.Stream.L s₀ - VG.Proof.ChaCha20.X86.Stream.H s₀ < 2 ^ 32 by omega)]
  have hnb : (VG.Proof.ChaCha20.X86.Stream.L s₀ - VG.Proof.ChaCha20.X86.Stream.H s₀) / 64 * 64 = 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀ := by simp only [VG.Proof.ChaCha20.X86.Stream.NB, blocksOf, VG.Proof.ChaCha20.X86.Stream.H]; omega
  rw [hnb]
  have hk4 : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → s₄.gpr r = s₃.gpr r := h₄.keep
  refine ⟨by simp (config := {decide := true}) [hk4 .ebx (by decide) (by decide) (by decide) (by decide), h₃.ebx],
    by simp (config := {decide := true}) [h₄.esi], by simp (config := {decide := true}) [hebp],
    by simp (config := {decide := true}), ?_,
    by simp (config := {decide := true}) [hk4 .esp (by decide) (by decide) (by decide) (by decide), h₃.esp],
    by rw [h₄.rd, h₃.rd], by rw [h₄.wr, h₃.wr], ⟨fun i hi => ?_, ?_⟩, fun k hk => ?_, ?_⟩
  · rw [ofNat32_beq_zero (by omega)]
  · rw [h₄.frame _ fun r hr hc => ?_]
    · exact h₃.mid.keep i hi
    · simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_d _ (Offset.contains_base (st s₀) (d := i) (n := 1) (k := 768) (by omega) (by omega))
        (Offset.sub_base (VG.Proof.ChaCha20.X86.Stream.dp s₀) (d := 0) (n := VG.Proof.ChaCha20.X86.Stream.H s₀) (k := VG.Proof.ChaCha20.X86.Stream.L s₀) (by omega) _ (by simpa using hc))
  · exact h₃.mid.saved.frame h₄.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.st_d.sub_left (VG.Proof.ChaCha20.X86.Stream.savR_sub s₀)).sub_right fun x hx => by
        simpa using Offset.sub_base (VG.Proof.ChaCha20.X86.Stream.dp s₀) (d := 0) (n := VG.Proof.ChaCha20.X86.Stream.H s₀) (k := VG.Proof.ChaCha20.X86.Stream.L s₀) (by omega) x (by simpa using hx)
  · dsimp only
    by_cases hk' : k < VG.Proof.ChaCha20.X86.Stream.H s₀
    · rw [h₄.data k hk', h₃.done k hk, eK, Offset.add_add, h₃.mid.keep _ (by omega)]
      simp [hk', VG.Proof.ChaCha20.X86.Stream.KS]
    · rw [h₄.frame _ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.ChaCha20.X86.Stream.not_in_prefix _ (by omega) (by omega),
        h₃.done k hk]
      simp [hk']
  · exact (h₃.frame.mono (by simp)).trans (h₄.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.ChaCha20.X86.Stream.dR s₀, by simp, VG.Proof.ChaCha20.X86.Stream.prefix_sub _ hH⟩)

theorem part1_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) (hle : VG.Proof.ChaCha20.X86.Stream.L s₀ ≤ VG.Proof.ChaCha20.X86.Stream.N s₀) {s : State} (h : VG.Proof.ChaCha20.X86.Stream.Q0 s₀ s) :
    WP isa part1 s (VG.Proof.ChaCha20.X86.Stream.Q1 s₀) := by
  rw [VG.Proof.ChaCha20.X86.Stream.part1_eq]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Stream.start_ok hp hle h) fun s₁ ⟨h₁, hc₁⟩ => ?_)
  exact WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Stream.sel_ok h₁ hc₁) fun s₂ h₂ => VG.Proof.ChaCha20.X86.Stream.rest1_ok hp h₂)

/-! ## The whole blocks -/

/-- The memory before the counter is advanced: the state copied to
`st + 192`, 16 bytes at a time. -/
def copyMem8 (m : Mem) (st : Addr) : Mem :=
  (((m.writeW (st + BitVec.ofNat 64 192) (m.readW (st + BitVec.ofNat 64 0) 128)).writeW (st + BitVec.ofNat 64 208)
    (m.readW (st + BitVec.ofNat 64 16) 128)).writeW (st + BitVec.ofNat 64 224) (m.readW (st + BitVec.ofNat 64 32) 128)).writeW
    (st + BitVec.ofNat 64 240) (m.readW (st + BitVec.ofNat 64 48) 128)

/-- And its counter advanced by `c`. -/
def copyMem (m : Mem) (st : Addr) (c : BitVec 32) : Mem :=
  (VG.Proof.ChaCha20.X86.Stream.copyMem8 m st).writeW (st + BitVec.ofNat 64 48) (c + m.readW (st + BitVec.ofNat 64 48) 32)

/-- The arguments of `vg_chacha20_xor`, after the copy. -/
structure Args (s₀ s : State) : Prop where
  edx : s.gpr .edx = ST s₀ + BitVec.ofNat 32 192
  esi : s.gpr .esi = VG.Proof.ChaCha20.X86.Stream.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.H s₀)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (64 * VG.Proof.ChaCha20.X86.Stream.NB s₀)
  eax : s.gpr .eax = ST s₀ + BitVec.ofNat 32 256
  edi : s.gpr .edi = BitVec.ofNat 32 (64 * VG.Proof.ChaCha20.X86.Stream.NB s₀)
  ebx : s.gpr .ebx = ST s₀
  ebp : s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.L s₀ - VG.Proof.ChaCha20.X86.Stream.H s₀)
  esp : s.gpr .esp = VG.Proof.ChaCha20.X86.Stream.E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem shr_eq {nb : Nat} (h : 64 * nb < 2 ^ 32) : BitVec.ofNat 32 (64 * nb) >>> 6 = BitVec.ofNat 32 nb := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow]
  omega

set_option simprocs false in
theorem args_exec {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.X86.Stream.Q1 s₀ s) :
    WP isa (.block blocksArgs) s fun s' => s'.mem = VG.Proof.ChaCha20.X86.Stream.copyMem s.mem (st s₀) (BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.NB s₀)) ∧ VG.Proof.ChaCha20.X86.Stream.Args s₀ s' := by
  have hL := VG.Proof.ChaCha20.X86.Stream.L_lt s₀
  have hHNB := VG.Proof.ChaCha20.X86.Stream.HNB_le s₀
  have e : ∀ d, d < 768 → (s.gpr .ebx + BitVec.ofNat 32 d).setWidth 64 = st s₀ + BitVec.ofNat 64 d :=
    fun d hd => by rw [h.ebx]; exact hp.eaS hd
  have o : ∀ d n, d + n ≤ 768 → InRegions s.wr (st s₀ + BitVec.ofNat 64 d) n := fun d n hd => by
    rw [h.wr]; exact hp.w_st hd
  have r : ∀ d n, d + n ≤ 768 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 d) n := fun d n hd => by
    rw [h.rd, h.wr]; exact hp.r_st hd
  have e0 := e 0 (by decide); have e16 := e 16 (by decide); have e32 := e 32 (by decide)
  have e48 := e 48 (by decide); have e192 := e 192 (by decide); have e208 := e 208 (by decide)
  have e224 := e 224 (by decide); have e240 := e 240 (by decide)
  have i0 := r 0 16 (by decide); have i16 := r 16 16 (by decide); have i32 := r 32 16 (by decide)
  have i48 := r 48 16 (by decide); have i48' := r 48 4 (by decide)
  have o192 := o 192 16 (by decide); have o208 := o 208 16 (by decide); have o224 := o 224 16 (by decide)
  have o240 := o 240 16 (by decide); have o48 := o 48 4 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [blocksArgs, ptr, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, exec, readSrc, State.ea, at_, State.load32, State.load128, State.store32,
    State.store128, execAlu, execShift, arithFlags, State.setReg, State.setXmm, State.setFlags, e0, e16, e32, e48,
    e192, e208, e224, e240, i0, i16, i32, i48, i48', o192, o208, o224, o240, o48, h.ecx,
    readW_writeW_ofNat, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', VG.Proof.ChaCha20.X86.Stream.shr_eq (show 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀ < 2 ^ 32 by omega)]
  refine ⟨rfl, by simp (config := {decide := true}) [h.ebx], by simp (config := {decide := true}) [h.esi],
    by simp (config := {decide := true}) [h.ecx], by simp (config := {decide := true}) [h.ebx],
    by simp (config := {decide := true}), by simp (config := {decide := true}) [h.ebx],
    by simp (config := {decide := true}) [h.ebp], by simp (config := {decide := true}) [h.esp], h.rd, h.wr⟩

theorem readW_writeW_self128 (m : Mem) (a : Addr) (v : BitVec 128) : (m.writeW a v).readW a 128 = v :=
  Mem.readW_writeW_self m a 16 v (by decide)

theorem copyMem8_frame (m : Mem) (st : Addr) : Frame [⟨st + BitVec.ofNat 64 192, 64⟩] m (VG.Proof.ChaCha20.X86.Stream.copyMem8 m st) := by
  have c : ∀ d, 192 ≤ d → d + 16 ≤ 256 →
      (⟨st + BitVec.ofNat 64 192, 64⟩ : Region).Contains (st + BitVec.ofNat 64 d) (128 / 8) :=
    fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 192 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (c 224 (by decide) (by decide))).writeW (List.mem_singleton_self _) _ (c 240 (by decide) (by decide))

theorem copyMem_frame (m : Mem) (st : Addr) (c : BitVec 32) :
    Frame [⟨st, 64⟩, ⟨st + BitVec.ofNat 64 192, 64⟩] m (VG.Proof.ChaCha20.X86.Stream.copyMem m st c) :=
  ((VG.Proof.ChaCha20.X86.Stream.copyMem8_frame m st).mono (by simp)).writeW (List.mem_cons_self ..) _ (Offset.contains_base _ (by omega) (by omega))

set_option simprocs false in
/-- The copy of the state. -/
theorem copyMem_copy (m : Mem) (st : Addr) (c : BitVec 32) :
    stateAt (VG.Proof.ChaCha20.X86.Stream.copyMem m st c) (st + BitVec.ofNat 64 192) = stateAt m st := by
  refine stateAt_congr fun i hi => ?_
  rw [VG.Proof.ChaCha20.X86.Stream.copyMem, Offset.add_add, byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)]
  have hw : ∀ k, 12 ≤ k → k < 16 → (VG.Proof.ChaCha20.X86.Stream.copyMem8 m st).readW (st + BitVec.ofNat 64 (16 * k)) 128 =
      m.readW (st + BitVec.ofNat 64 (16 * (k - 12))) 128 := by
    intro k h₁ h₂
    simp only [VG.Proof.ChaCha20.X86.Stream.copyMem8]
    obtain rfl | rfl | rfl | rfl : k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
    all_goals simp (config := {decide := true}) only [VG.Proof.ChaCha20.X86.Stream.readW_writeW_self128,
      readW_writeW_ofNat]
  have hm : ∀ k, 0 ≤ k → k < 4 → m.readW (st + BitVec.ofNat 64 (16 * k)) 128 =
      m.readW (st + BitVec.ofNat 64 (16 * k)) 128 := fun _ _ _ => rfl
  rw [byte_of_words128 hw (by omega) (by omega), byte_of_words128 hm (i := i) (Nat.zero_le _) (by omega),
    show (192 + i) / 16 - 12 = i / 16 by omega, show (192 + i) % 16 = i % 16 by omega]

/-- The state, with its counter advanced. -/
theorem copyMem_state (m : Mem) (st : Addr) (c : BitVec 32) :
    stateAt (VG.Proof.ChaCha20.X86.Stream.copyMem m st c) st = (stateAt m st).set 12 ((stateAt m st)[12] + c) := by
  rw [VG.Proof.ChaCha20.X86.Stream.copyMem, Proof.ChaCha20.X86.Xor.stateAt_writeW_counter,
    Proof.ChaCha20.X86.Xor.stateAt_frame (VG.Proof.ChaCha20.X86.Stream.copyMem8_frame m st) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ (by omega) (by omega)), BitVec.add_comm]
  simp [stateAt]

/-- After `part2`: the whole blocks XORed, and the counter advanced past
them. -/
structure Q2 (s₀ s : State) : Prop where
  ebx : s.gpr .ebx = ST s₀
  esi : s.gpr .esi = VG.Proof.ChaCha20.X86.Stream.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.T s₀)
  esp : s.gpr .esp = VG.Proof.ChaCha20.X86.Stream.E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : stateAt s.mem (st s₀) = ctr (VG.Proof.ChaCha20.X86.Stream.S0 s₀) (VG.Proof.ChaCha20.X86.Stream.NB s₀)
  buf : ∀ i < 64, s.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₀.mem (st s₀ + BitVec.ofNat 64 (64 + i))
  saved : VG.Proof.ChaCha20.X86.Stream.Saved s₀ s.mem
  done : VG.Proof.ChaCha20.X86.Stream.Done s₀ (VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀) s.mem
  frame : Frame [VG.Proof.ChaCha20.X86.Stream.stR s₀, VG.Proof.ChaCha20.X86.Stream.dR s₀, VG.Proof.ChaCha20.X86.Stream.stkR s₀] s₀.mem s.mem

theorem nb_zero_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20.X86.Stream.Q1 s₀ s) (h0 : 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀ = 0) : VG.Proof.ChaCha20.X86.Stream.Q2 s₀ s := by
  have hT := VG.Proof.ChaCha20.X86.Stream.T_eq s₀
  refine ⟨h.ebx, by rw [h.esi, h0, Nat.add_zero], by rw [h.ebp, hT, h0, Nat.sub_zero], h.esp, h.rd, h.wr,
    by rw [h.mid.state, show VG.Proof.ChaCha20.X86.Stream.NB s₀ = 0 by omega, ctr_zero], fun i hi => h.mid.keep _ (by omega), h.mid.saved,
    by rw [h0, Nat.add_zero]; exact h.done, h.frame.mono (by simp)⟩

theorem part2_eq (v : Impl.ChaCha20.X86.Callee) : part2 v = .ite .e (.block [])
    (.seq (.block blocksArgs) (.seq (callXor v) (.block [.alu .add .esi (.reg .edi), .alu .sub .ebp (.reg .edi)]))) := rfl

set_option simprocs false in
theorem blocks_ok (v : XorImpl) {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.X86.Stream.Q1 s₀ s) (hnb : 0 < VG.Proof.ChaCha20.X86.Stream.NB s₀) :
    WP isa (.seq (.block blocksArgs) (.seq (callXor v.callee) (.block [.alu .add .esi (.reg .edi), .alu .sub .ebp (.reg .edi)])))
      s (VG.Proof.ChaCha20.X86.Stream.Q2 s₀) := by
  have hL := VG.Proof.ChaCha20.X86.Stream.L_lt s₀
  have hH := VG.Proof.ChaCha20.X86.Stream.H_le s₀
  have hHNB := VG.Proof.ChaCha20.X86.Stream.HNB_le s₀
  have hT := VG.Proof.ChaCha20.X86.Stream.T_eq s₀
  have hd := hp.d_fit
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Stream.args_exec hp h) fun s₁ ⟨m₁, a₁⟩ => ?_)
  refine WP.seq (VG.Proof.ChaCha20.X86.Stream.xor_call v hp ⟨a₁.esp, a₁.rd, a₁.wr⟩ hnb a₁.edx a₁.esi a₁.ecx a₁.eax fun s₂ at₂ cs₂ f₂ x₂ => ?_)
  have g : ∀ r ∈ [Reg.ebx, .esi, .edi, .ebp, .esp], s₂.gpr r = s₁.gpr r :=
    fun r hr => cs₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])
  have gsi := g .esi (by simp); have gdi := g .edi (by simp); have gbp := g .ebp (by simp)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_false, gsi, gdi, gbp, a₁.esi, a₁.edi, a₁.ebp]
  -- Regions the call does not write.
  have nd : ∀ R : Region, R.Disjoint (VG.Proof.ChaCha20.X86.Stream.cpR s₀) → R.Disjoint (VG.Proof.ChaCha20.X86.Stream.blR s₀) → R.Disjoint (VG.Proof.ChaCha20.X86.Stream.wkR s₀) →
      R.Disjoint (VG.Proof.ChaCha20.X86.Stream.stkR s₀) → ∀ r ∈ [VG.Proof.ChaCha20.X86.Stream.cpR s₀, VG.Proof.ChaCha20.X86.Stream.blR s₀, VG.Proof.ChaCha20.X86.Stream.wkR s₀, VG.Proof.ChaCha20.X86.Stream.stkR s₀], R.Disjoint r := by
    intro R h₁ h₂ h₃ h₄ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h₁, h₂, h₃, h₄]
  have nc : ∀ R : Region, R.Disjoint ⟨st s₀, 64⟩ → R.Disjoint ⟨st s₀ + BitVec.ofNat 64 192, 64⟩ →
      ∀ r ∈ [⟨st s₀, 64⟩, ⟨st s₀ + BitVec.ofNat 64 192, 64⟩], R.Disjoint r := by
    intro R h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h₁, h₂]
  have fc := VG.Proof.ChaCha20.X86.Stream.copyMem_frame s.mem (st s₀) (BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.NB s₀))
  rw [← m₁] at fc
  have stS : Region.Sub ⟨st s₀, 64⟩ (VG.Proof.ChaCha20.X86.Stream.stR s₀) := VG.Proof.ChaCha20.X86.Stream.prefix_sub _ (by omega)
  have cpS : Region.Sub ⟨st s₀ + BitVec.ofNat 64 192, 64⟩ (VG.Proof.ChaCha20.X86.Stream.stR s₀) := VG.Proof.ChaCha20.X86.Stream.cpR_sub s₀
  have bufS : Region.Sub ⟨st s₀ + BitVec.ofNat 64 64, 64⟩ (VG.Proof.ChaCha20.X86.Stream.stR s₀) := Offset.sub_base _ (by omega)
  have svS := VG.Proof.ChaCha20.X86.Stream.savR_sub s₀
  have sd : ∀ R, Region.Sub R (VG.Proof.ChaCha20.X86.Stream.stR s₀) → R.Disjoint (VG.Proof.ChaCha20.X86.Stream.blR s₀) := fun R hR =>
    (hp.st_d.sub_left hR).sub_right (VG.Proof.ChaCha20.X86.Stream.blR_sub s₀)
  have sk : ∀ R, Region.Sub R (VG.Proof.ChaCha20.X86.Stream.stR s₀) → R.Disjoint (VG.Proof.ChaCha20.X86.Stream.stkR s₀) := fun R hR => hp.stk_st.symm.sub_left hR
  have ds : ∀ R R', Region.Sub R (VG.Proof.ChaCha20.X86.Stream.dR s₀) → Region.Sub R' (VG.Proof.ChaCha20.X86.Stream.stR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.symm.sub_left h₁).sub_right h₂
  have dk : ∀ R, Region.Sub R (VG.Proof.ChaCha20.X86.Stream.dR s₀) → R.Disjoint (VG.Proof.ChaCha20.X86.Stream.stkR s₀) := fun R hR => hp.stk_d.symm.sub_left hR
  refine ⟨by simp (config := {decide := true}) [g .ebx (by simp), a₁.ebx], ?_, ?_,
    by simp (config := {decide := true}) [g .esp (by simp), a₁.esp], by rw [at₂.rd], by rw [at₂.wr], ?_,
    fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · simp (config := {decide := true}) only [ite_true, ite_false]
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  · simp (config := {decide := true}) only [ite_true, ite_false]
    rw [VG.Proof.ChaCha20.X86.Stream.sub_ofNat32 (by omega), hT, Nat.sub_sub]
  · rw [Proof.ChaCha20.X86.Xor.stateAt_frame f₂ (nd _
        (Offset.base_disjoint _ (by omega) (by omega)) (sd _ stS)
        (Offset.base_disjoint _ (by omega) (by omega)) (sk _ stS)),
      m₁, VG.Proof.ChaCha20.X86.Stream.copyMem_state, h.mid.state]
    rfl
  · rw [← Offset.add_add, f₂.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (nd _
        (Offset.disjoint _ (by omega) (by omega) (by omega)) (sd _ bufS)
        (Offset.disjoint _ (by omega) (by omega) (by omega)) (sk _ bufS)) (show 64 ≤ 2 ^ 64 by decide) hi,
      fc.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (nc _ (Offset.disjoint_base _ (by omega) (by omega))
        (Offset.disjoint _ (by omega) (by omega) (by omega))) (show 64 ≤ 2 ^ 64 by decide) hi,
      Offset.add_add]
    exact h.mid.keep _ (by omega)
  · refine (h.mid.saved.frame fc (nc _ ?_ ?_)).frame f₂ (nd _ ?_ (sd _ svS) ?_ (sk _ svS))
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · have fcd : s₁.mem (VG.Proof.ChaCha20.X86.Stream.dp s₀ + BitVec.ofNat 64 k) = s.mem (VG.Proof.ChaCha20.X86.Stream.dp s₀ + BitVec.ofNat 64 k) :=
      fc.bytes (R := VG.Proof.ChaCha20.X86.Stream.dR s₀) (nc _ (ds _ _ (fun _ h => h) stS) (ds _ _ (fun _ h => h) cpS))
        (show VG.Proof.ChaCha20.X86.Stream.L s₀ ≤ 2 ^ 64 by omega) hk
    by_cases hk₁ : k < VG.Proof.ChaCha20.X86.Stream.H s₀
    · have hpre : Region.Sub ⟨VG.Proof.ChaCha20.X86.Stream.dp s₀, VG.Proof.ChaCha20.X86.Stream.H s₀⟩ (VG.Proof.ChaCha20.X86.Stream.dR s₀) := VG.Proof.ChaCha20.X86.Stream.prefix_sub _ hH
      rw [f₂.bytes (R := ⟨VG.Proof.ChaCha20.X86.Stream.dp s₀, VG.Proof.ChaCha20.X86.Stream.H s₀⟩) (nd _ (ds _ _ hpre (VG.Proof.ChaCha20.X86.Stream.cpR_sub s₀))
          (Offset.base_disjoint _ (by omega) (by omega)) (ds _ _ hpre (VG.Proof.ChaCha20.X86.Stream.wkR_sub s₀)) (dk _ hpre))
          (show VG.Proof.ChaCha20.X86.Stream.H s₀ ≤ 2 ^ 64 by omega) hk₁]
      rw [fcd, h.done k hk, ite_pos hk₁, ite_pos (by omega)]
    by_cases hk₂ : k < VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀
    · have e := xor_getD (length_keystream _ _) x₂ (j := k - VG.Proof.ChaCha20.X86.Stream.H s₀) (by omega)
      rw [Offset.add_add, show VG.Proof.ChaCha20.X86.Stream.H s₀ + (k - VG.Proof.ChaCha20.X86.Stream.H s₀) = k by omega, fcd, h.done k hk, ite_neg hk₁, m₁,
        VG.Proof.ChaCha20.X86.Stream.copyMem_copy, h.mid.state, keystream_getD _ (by omega)] at e
      rw [e, ite_pos hk₂]
      simp only [VG.Proof.ChaCha20.X86.Stream.KS, ite_neg hk₁]
    · have hR : Region.Sub ⟨VG.Proof.ChaCha20.X86.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀), VG.Proof.ChaCha20.X86.Stream.L s₀ - (VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀)⟩ (VG.Proof.ChaCha20.X86.Stream.dR s₀) :=
        Offset.sub_base _ (by omega)
      have := f₂.bytes (R := ⟨VG.Proof.ChaCha20.X86.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀), VG.Proof.ChaCha20.X86.Stream.L s₀ - (VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀)⟩)
        (nd _ (ds _ _ hR (VG.Proof.ChaCha20.X86.Stream.cpR_sub s₀)) (Offset.disjoint _ (by omega) (by omega) (by omega))
          (ds _ _ hR (VG.Proof.ChaCha20.X86.Stream.wkR_sub s₀)) (dk _ hR)) (show VG.Proof.ChaCha20.X86.Stream.L s₀ - (VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀) ≤ 2 ^ 64 by omega)
          (i := k - (VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀)) (by simp only; omega)
      rw [Offset.add_add, show VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀ + (k - (VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀)) = k by omega] at this
      rw [this, fcd, h.done k hk, ite_neg hk₁, ite_neg hk₂]
  · refine ((h.frame.mono (by simp)).trans (fc.sub fun r hr => ?_)).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.ChaCha20.X86.Stream.stR s₀, by simp, stS⟩
      · exact ⟨VG.Proof.ChaCha20.X86.Stream.stR s₀, by simp, cpS⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨VG.Proof.ChaCha20.X86.Stream.stR s₀, by simp, VG.Proof.ChaCha20.X86.Stream.cpR_sub s₀⟩
      · exact ⟨VG.Proof.ChaCha20.X86.Stream.dR s₀, by simp, VG.Proof.ChaCha20.X86.Stream.blR_sub s₀⟩
      · exact ⟨VG.Proof.ChaCha20.X86.Stream.stR s₀, by simp, VG.Proof.ChaCha20.X86.Stream.wkR_sub s₀⟩
      · exact ⟨VG.Proof.ChaCha20.X86.Stream.stkR s₀, by simp, fun _ h => h⟩

theorem part2_ok (v : XorImpl) {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.X86.Stream.Q1 s₀ s) :
    WP isa (part2 v.callee) s (VG.Proof.ChaCha20.X86.Stream.Q2 s₀) := by
  rw [VG.Proof.ChaCha20.X86.Stream.part2_eq]
  refine WP.ite (decide (64 * VG.Proof.ChaCha20.X86.Stream.NB s₀ = 0)) (by show eval .e s = _; simp only [eval, h.zf])
    (fun h0 => WP.block_nil (M := isa) (VG.Proof.ChaCha20.X86.Stream.nb_zero_ok h (by simpa using h0)))
    (fun h0 => VG.Proof.ChaCha20.X86.Stream.blocks_ok v hp h (by simp at h0; omega))

/-! ## The last bytes -/

/-- After `part3`: all the data XORed; the counter advanced past the block
started, if any, which is buffered. -/
structure Q3 (s₀ s : State) : Prop where
  ebx : s.gpr .ebx = ST s₀
  esp : s.gpr .esp = VG.Proof.ChaCha20.X86.Stream.E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : stateAt s.mem (st s₀) = ctr (VG.Proof.ChaCha20.X86.Stream.S0 s₀) (VG.Proof.ChaCha20.X86.Stream.NB s₀ + if VG.Proof.ChaCha20.X86.Stream.T s₀ = 0 then 0 else 1)
  buf : ∀ i < 64, s.mem (st s₀ + BitVec.ofNat 64 (64 + i)) =
    if VG.Proof.ChaCha20.X86.Stream.T s₀ = 0 then s₀.mem (st s₀ + BitVec.ofNat 64 (64 + i))
    else (serialize (block (ctr (VG.Proof.ChaCha20.X86.Stream.S0 s₀) (VG.Proof.ChaCha20.X86.Stream.NB s₀)))).getD i 0
  saved : VG.Proof.ChaCha20.X86.Stream.Saved s₀ s.mem
  done : VG.Proof.ChaCha20.X86.Stream.Done s₀ (VG.Proof.ChaCha20.X86.Stream.L s₀) s.mem
  frame : Frame [VG.Proof.ChaCha20.X86.Stream.stR s₀, VG.Proof.ChaCha20.X86.Stream.dR s₀, VG.Proof.ChaCha20.X86.Stream.stkR s₀] s₀.mem s.mem

theorem t_zero_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20.X86.Stream.Q2 s₀ s) (h0 : VG.Proof.ChaCha20.X86.Stream.T s₀ = 0) : VG.Proof.ChaCha20.X86.Stream.Q3 s₀ s := by
  have hT := VG.Proof.ChaCha20.X86.Stream.T_eq s₀
  have hHNB := VG.Proof.ChaCha20.X86.Stream.HNB_le s₀
  refine ⟨h.ebx, h.esp, h.rd, h.wr, by rw [h.state, h0]; rfl, fun i hi => by rw [h.buf i hi, h0]; rfl, h.saved,
    by rw [show VG.Proof.ChaCha20.X86.Stream.L s₀ = VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀ by omega]; exact h.done, h.frame⟩

/-- The buffered block, and the bytes the block function may write. -/
abbrev bufR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 64, 256⟩

theorem bufR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.X86.Stream.bufR s₀) (VG.Proof.ChaCha20.X86.Stream.stR s₀) := Offset.sub_base _ (by omega)

set_option simprocs false in
theorem tailPtr_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20.X86.Stream.Q2 s₀ s) :
    WP isa (.block (ptr .eax .ebx 64)) s fun s' => s'.gpr .eax = ST s₀ + BitVec.ofNat 32 64 ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [ptr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', ite_true, h.ebx]
  exact ⟨trivial, fun r hr => by simp [hr], trivial⟩

set_option simprocs false in
/-- The counter advanced, and the arguments of `xorBytes` for the buffered
block. -/
theorem ctr_exec {s : State} {S : BitVec 32} (hebx : s.gpr .ebx = S)
    (he : (S + BitVec.ofNat 32 48).setWidth 64 = S.setWidth 64 + BitVec.ofNat 64 48)
    (hw : InRegions s.wr (S.setWidth 64 + BitVec.ofNat 64 48) 4)
    (hr : InRegions (s.rd ++ s.wr) (S.setWidth 64 + BitVec.ofNat 64 48) 4) :
    WP isa (.block (([.mov .eax (.mem (at_ .ebx 48)), .alu .add .eax (.imm 1), .store (at_ .ebx 48) .eax] : List Instr) ++
      ptr .edx .ebx 64 ++ ([.mov .ecx (.reg .ebp)] : List Instr))) s fun s' =>
      s'.mem = s.mem.writeW (S.setWidth 64 + BitVec.ofNat 64 48) (s.mem.readW (S.setWidth 64 + BitVec.ofNat 64 48) 32 + 1) ∧
      s'.gpr .edx = S + BitVec.ofNat 32 64 ∧ s'.gpr .ecx = s.gpr .ebp ∧
      (∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [ptr, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, State.ea, at_, State.load32, State.store32, execAlu, arithFlags, State.setReg,
    State.setFlags, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', ite_true, ite_false,
    hebx, he, hw, hr]
  exact ⟨trivial, trivial, trivial, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃], trivial⟩

theorem tailXor_eq : tailXor = .seq (.block (([.mov .eax (.mem (at_ .ebx 48)), .alu .add .eax (.imm 1),
    .store (at_ .ebx 48) .eax] : List Instr) ++ ptr .edx .ebx 64 ++ ([.mov .ecx (.reg .ebp)] : List Instr))) xorBytes := rfl

set_option simprocs false in
theorem tail_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.X86.Stream.Q2 s₀ s) (ht : VG.Proof.ChaCha20.X86.Stream.T s₀ ≠ 0) :
    WP isa (.seq (.block (ptr .eax .ebx 64)) (.seq callBlock tailXor)) s (VG.Proof.ChaCha20.X86.Stream.Q3 s₀) := by
  have hT := VG.Proof.ChaCha20.X86.Stream.T_eq s₀
  have hHNB := VG.Proof.ChaCha20.X86.Stream.HNB_le s₀
  have hL := VG.Proof.ChaCha20.X86.Stream.L_lt s₀
  have hd := hp.d_fit
  have hst := hp.st_fit
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Stream.tailPtr_ok h) fun s₁ ⟨eax₁, k₁, m₁, rd₁, wr₁⟩ => ?_)
  have at₁ : VG.Proof.ChaCha20.X86.Stream.At s₀ s₁ := ⟨by rw [k₁ _ (by decide), h.esp], by rw [rd₁, h.rd], by rw [wr₁, h.wr]⟩
  refine WP.seq (VG.Proof.ChaCha20.X86.Stream.block_call hp at₁ (by rw [k₁ _ (by decide), h.ebx]) eax₁ fun s₂ at₂ cs₂ f₂ blk₂ => ?_)
  have g : ∀ r ∈ [Reg.ebx, .esi, .edi, .ebp, .esp], s₂.gpr r = s.gpr r := fun r hr => by
    rw [cs₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact k₁ r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  have hwr₂ : s₂.wr = [VG.Proof.ChaCha20.X86.Stream.stR s₀, VG.Proof.ChaCha20.X86.Stream.dR s₀, VG.Proof.ChaCha20.X86.Stream.aR s₀] := by rw [at₂.wr, hp.wr]
  have hrd₂ : s₂.rd = [] := by rw [at₂.rd, hp.rd]
  have hw48 : InRegions s₂.wr (st s₀ + BitVec.ofNat 64 48) 4 := by rw [at₂.wr]; exact hp.w_st (by decide)
  have hr48 : InRegions (s₂.rd ++ s₂.wr) (st s₀ + BitVec.ofNat 64 48) 4 := by
    rw [at₂.rd, at₂.wr]; exact hp.r_st (by decide)
  rw [VG.Proof.ChaCha20.X86.Stream.tailXor_eq]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Stream.ctr_exec (by rw [g .ebx (by simp), h.ebx]) (hp.eaS (by decide)) hw48 hr48)
    fun s₃ ⟨m₃, edx₃, ecx₃, k₃, rd₃, wr₃⟩ => ?_)
  have hT64 : VG.Proof.ChaCha20.X86.Stream.T s₀ < 64 := Nat.mod_lt _ (by decide)
  have hesi₃ : s₃.gpr .esi = VG.Proof.ChaCha20.X86.Stream.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀) := by
    rw [k₃ .esi (by decide) (by decide) (by decide), g .esi (by simp), h.esi]
  have dS : ∀ R R', Region.Sub R (VG.Proof.ChaCha20.X86.Stream.dR s₀) → Region.Sub R' (VG.Proof.ChaCha20.X86.Stream.stR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.symm.sub_left h₁).sub_right h₂
  have eD : (VG.Proof.ChaCha20.X86.Stream.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀)).setWidth 64 = VG.Proof.ChaCha20.X86.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀) :=
    hp.eaD (by omega)
  have eK : (ST s₀ + BitVec.ofNat 32 64).setWidth 64 = st s₀ + BitVec.ofNat 64 64 := hp.eaS (by decide)
  have hb : BPre s₃ (VG.Proof.ChaCha20.X86.Stream.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀)) (ST s₀ + BitVec.ofNat 32 64) (VG.Proof.ChaCha20.X86.Stream.T s₀) :=
    ⟨hesi₃, edx₃, by rw [ecx₃, g .ebp (by simp), h.ebp], by rw [hp.dNat (by omega)]; omega,
      by rw [hp.sNat (by decide)]; omega,
      fun k hk => by
        rw [wr₃, at₂.wr, hp.wr, eD, Offset.add_add]
        exact ⟨VG.Proof.ChaCha20.X86.Stream.dR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun k hk => by rw [rd₃, wr₃, at₂.rd, at₂.wr, eK, Offset.add_add]; exact hp.r_st (by omega),
      fun j hj k hk => by rw [eD, eK, Offset.add_add, Offset.add_add]; exact VG.Proof.ChaCha20.X86.Stream.d_ne_st hp (by omega) (by omega)⟩
  refine WP.mono (xorBytes_ok hb) fun s₄ h₄ => ?_
  have stS : Region.Sub ⟨st s₀, 64⟩ (VG.Proof.ChaCha20.X86.Stream.stR s₀) := VG.Proof.ChaCha20.X86.Stream.prefix_sub _ (by omega)
  have f₃ : Frame [⟨st s₀ + BitVec.ofNat 64 48, 4⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have tR : Region.Sub ⟨VG.Proof.ChaCha20.X86.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀), VG.Proof.ChaCha20.X86.Stream.T s₀⟩ (VG.Proof.ChaCha20.X86.Stream.dR s₀) := Offset.sub_base _ (by omega)
  have c48 : Region.Sub ⟨st s₀ + BitVec.ofNat 64 48, 4⟩ (VG.Proof.ChaCha20.X86.Stream.stR s₀) := Offset.sub_base _ (by omega)
  have st₂ : stateAt s₂.mem (st s₀) = ctr (VG.Proof.ChaCha20.X86.Stream.S0 s₀) (VG.Proof.ChaCha20.X86.Stream.NB s₀) := by
    rw [Proof.ChaCha20.X86.Xor.stateAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.base_disjoint _ (by omega) (by omega)
        · exact hp.stk_st.symm.sub_left stS),
      m₁, h.state]
  have bb : ∀ i < 64, s₂.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = (serialize (block (ctr (VG.Proof.ChaCha20.X86.Stream.S0 s₀) (VG.Proof.ChaCha20.X86.Stream.NB s₀)))).getD i 0 := by
    intro i hi
    rw [← Offset.add_add, ← serialize_stateAt s₂.mem _ hi, blk₂, m₁, h.state]
  have b3 : ∀ i < 64, s₃.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₂.mem (st s₀ + BitVec.ofNat 64 (64 + i)) := by
    intro i hi
    rw [m₃]; exact byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)
  have b4 : ∀ i < 64, s₄.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₃.mem (st s₀ + BitVec.ofNat 64 (64 + i)) := by
    intro i hi
    rw [← Offset.add_add]
    exact h₄.frame.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [eD]; exact (dS _ _ tR (Offset.sub_base _ (by omega))).symm) (show 64 ≤ 2 ^ 64 by decide) hi
  have f₄ : Frame [⟨VG.Proof.ChaCha20.X86.Stream.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀), VG.Proof.ChaCha20.X86.Stream.T s₀⟩] s₃.mem s₄.mem := by
    have := h₄.frame; rwa [eD] at this
  refine ⟨?_, ?_, by rw [h₄.rd, rd₃, at₂.rd], by rw [h₄.wr, wr₃, at₂.wr], ?_,
    fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [h₄.keep _ (by decide) (by decide) (by decide) (by decide),
      k₃ .ebx (by decide) (by decide) (by decide), g .ebx (by simp), h.ebx]
  · rw [h₄.keep _ (by decide) (by decide) (by decide) (by decide),
      k₃ .esp (by decide) (by decide) (by decide), g .esp (by simp), h.esp]
  · have e12 : s₂.mem.readW (st s₀ + BitVec.ofNat 64 48) 32 = (ctr (VG.Proof.ChaCha20.X86.Stream.S0 s₀) (VG.Proof.ChaCha20.X86.Stream.NB s₀))[12] := by
      rw [← st₂]; simp [stateAt]
    rw [Proof.ChaCha20.X86.Xor.stateAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dS _ _ tR stS).symm),
      m₃, Proof.ChaCha20.X86.Xor.stateAt_writeW_counter, st₂, e12, ctr_succ, ite_neg ht]
  · rw [b4 i hi, b3 i hi, bb i hi, ite_neg ht]
  · have svS := VG.Proof.ChaCha20.X86.Stream.savR_sub s₀
    rw [m₁] at f₂
    refine ((h.saved.frame f₂ fun r hr => ?_).frame f₃ fun r hr => ?_).frame f₄ fun r hr => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact hp.stk_st.symm.sub_left svS
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact (dS _ _ tR svS).symm
  · have dS48 : (VG.Proof.ChaCha20.X86.Stream.dR s₀).Disjoint ⟨st s₀ + BitVec.ofNat 64 48, 4⟩ := dS _ _ (fun _ h => h) c48
    have back : s₃.mem (VG.Proof.ChaCha20.X86.Stream.dp s₀ + BitVec.ofNat 64 k) = s.mem (VG.Proof.ChaCha20.X86.Stream.dp s₀ + BitVec.ofNat 64 k) := by
      rw [f₃.bytes (R := VG.Proof.ChaCha20.X86.Stream.dR s₀) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dS48)
          (show VG.Proof.ChaCha20.X86.Stream.L s₀ ≤ 2 ^ 64 by omega) hk,
        f₂.bytes (R := VG.Proof.ChaCha20.X86.Stream.dR s₀) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact dS _ _ (fun _ h => h) (VG.Proof.ChaCha20.X86.Stream.bufR_sub s₀)
          · exact hp.stk_d.symm) (show VG.Proof.ChaCha20.X86.Stream.L s₀ ≤ 2 ^ 64 by omega) hk, m₁]
    by_cases hk₁ : k < VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀
    · rw [f₄.bytes (R := ⟨VG.Proof.ChaCha20.X86.Stream.dp s₀, VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint _ (by omega) (by omega)) (show VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀ ≤ 2 ^ 64 by omega) hk₁,
        back, h.done k hk, ite_pos hk₁, ite_pos hk]
    · have e := h₄.data (k - (VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀)) (by omega)
      rw [eD, eK, Offset.add_add, Offset.add_add, show VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀ + (k - (VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀)) = k by omega,
        back, b3 _ (by omega), bb _ (by omega), h.done k hk, ite_neg hk₁] at e
      rw [e, ite_pos hk]
      simp only [VG.Proof.ChaCha20.X86.Stream.KS, ite_neg (show ¬ k < VG.Proof.ChaCha20.X86.Stream.H s₀ by omega)]
      rw [show (k - VG.Proof.ChaCha20.X86.Stream.H s₀) / 64 = VG.Proof.ChaCha20.X86.Stream.NB s₀ by omega, show (k - VG.Proof.ChaCha20.X86.Stream.H s₀) % 64 = k - (VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀) by omega]
  · rw [m₁] at f₂
    refine ((h.frame.trans (f₂.sub fun r hr => ?_)).trans (f₃.sub fun r hr => ?_)).trans
      (f₄.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.ChaCha20.X86.Stream.stR s₀, by simp, VG.Proof.ChaCha20.X86.Stream.bufR_sub s₀⟩
      · exact ⟨VG.Proof.ChaCha20.X86.Stream.stkR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.ChaCha20.X86.Stream.stR s₀, by simp, c48⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.ChaCha20.X86.Stream.dR s₀, by simp, tR⟩

theorem part3_eq : part3 = .seq (.block [.alu .test .ebp (.reg .ebp)])
    (.ite .e (.block []) (.seq (.block (ptr .eax .ebx 64)) (.seq callBlock tailXor))) := rfl

set_option simprocs false in
theorem test_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20.X86.Stream.Q2 s₀ s) :
    WP isa (.block [.alu .test .ebp (.reg .ebp)]) s fun s₁ => VG.Proof.ChaCha20.X86.Stream.Q2 s₀ s₁ ∧ s₁.zf = some (decide (VG.Proof.ChaCha20.X86.Stream.T s₀ = 0)) := by
  have hT64 : VG.Proof.ChaCha20.X86.Stream.T s₀ < 64 := Nat.mod_lt _ (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨h.ebx, h.esi, h.ebp, h.esp, h.rd, h.wr, h.state, h.buf, h.saved, h.done, h.frame⟩, ?_⟩
  rw [BitVec.and_self, h.ebp, ofNat32_beq_zero (by omega)]

theorem part3_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) {s : State} (h : VG.Proof.ChaCha20.X86.Stream.Q2 s₀ s) : WP isa part3 s (VG.Proof.ChaCha20.X86.Stream.Q3 s₀) := by
  rw [VG.Proof.ChaCha20.X86.Stream.part3_eq]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Stream.test_ok h) fun s₁ ⟨h₁, hz⟩ => ?_)
  refine WP.ite (decide (VG.Proof.ChaCha20.X86.Stream.T s₀ = 0)) (by show eval .e s₁ = _; simp only [eval, hz])
    (fun h0 => WP.block_nil (M := isa) (VG.Proof.ChaCha20.X86.Stream.t_zero_ok h₁ (by simpa using h0)))
    (fun h0 => VG.Proof.ChaCha20.X86.Stream.tail_ok hp h₁ (by simpa using h0))

/-! ## The end -/

theorem retR_stkR (s₀ : State) (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) : (VG.Proof.ChaCha20.X86.Stream.retR s₀).Disjoint (VG.Proof.ChaCha20.X86.Stream.stkR s₀) := by
  have := hp.sp_lo
  have := hp.sp_hi
  simp only [VG.Proof.ChaCha20.X86.Stream.retR, VG.Proof.ChaCha20.X86.Stream.stkR, below]
  rw [hp.E64 (by decide)]
  exact Offset.base_disjoint_below _ (n := 32) (k := 4) (by decide)

set_option simprocs false in
theorem finish_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) (hle : VG.Proof.ChaCha20.X86.Stream.L s₀ ≤ VG.Proof.ChaCha20.X86.Stream.N s₀) {s : State} (h : VG.Proof.ChaCha20.X86.Stream.Q3 s₀ s) :
    WP isa (.block finish) s (VG.Proof.ChaCha20.X86.Stream.Final s₀) := by
  have hL := VG.Proof.ChaCha20.X86.Stream.L_lt s₀
  have hN := VG.Proof.ChaCha20.X86.Stream.N_lt s₀
  have e : ∀ d, d < 768 → (s.gpr .ebx + BitVec.ofNat 32 d).setWidth 64 = st s₀ + BitVec.ofNat 64 d :=
    fun d hd => by rw [h.ebx]; exact hp.eaS hd
  have w : ∀ d, d + 4 ≤ 768 → InRegions s.wr (st s₀ + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [h.wr]; exact hp.w_st hd
  have r : ∀ d, d + 4 ≤ 768 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [h.rd, h.wr]; exact hp.r_st hd
  have e128 := e 128 (by decide); have e132 := e 132 (by decide); have e576 := e 576 (by decide)
  have e580 := e 580 (by decide); have e584 := e 584 (by decide); have e588 := e 588 (by decide)
  have e600 := e 600 (by decide); have e604 := e 604 (by decide)
  have o128 := w 128 (by decide); have o132 := w 132 (by decide)
  have i576 := r 576 (by decide); have i580 := r 580 (by decide); have i584 := r 584 (by decide)
  have i588 := r 588 (by decide); have i600 := r 600 (by decide); have i604 := r 604 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [finish, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.ea, at_, State.load32, State.store32, State.setReg, Option.map_some, Option.some.injEq,
    exists_eq_left', ite_true, ite_false, e128, e132, e576, e580, e584, e588, e600, e604, o128, o132, i576, i580,
    i584, i588, i600, i604, readW_writeW_ofNat, h.saved.lo, h.saved.hi, h.saved.ebx, h.saved.esi, h.saved.edi,
    h.saved.ebp]
  have hfw : Frame [⟨st s₀ + BitVec.ofNat 64 128, 8⟩] s.mem
      ((s.mem.writeW (st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.N s₀ - VG.Proof.ChaCha20.X86.Stream.L s₀))).writeW
        (st s₀ + BitVec.ofNat 64 132) (BitVec.ofNat 32 ((VG.Proof.ChaCha20.X86.Stream.N s₀ - VG.Proof.ChaCha20.X86.Stream.L s₀) / 2 ^ 32))) :=
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (st s₀) (e := 128) (d := 128) (k := 8) (by omega) (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains (st s₀) (e := 128) (d := 132) (k := 8) (by omega) (by omega) (by omega))
  have c128 : Region.Sub ⟨st s₀ + BitVec.ofNat 64 128, 8⟩ (VG.Proof.ChaCha20.X86.Stream.stR s₀) := Offset.sub_base _ (by omega)
  have hF := h.frame.trans (hfw.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.ChaCha20.X86.Stream.stR s₀, by simp, c128⟩)
  have hS : stateAt ((s.mem.writeW (st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.N s₀ - VG.Proof.ChaCha20.X86.Stream.L s₀))).writeW
      (st s₀ + BitVec.ofNat 64 132) (BitVec.ofNat 32 ((VG.Proof.ChaCha20.X86.Stream.N s₀ - VG.Proof.ChaCha20.X86.Stream.L s₀) / 2 ^ 32))) (st s₀) =
      ctr (VG.Proof.ChaCha20.X86.Stream.S0 s₀) (VG.Proof.ChaCha20.X86.Stream.NB s₀ + if VG.Proof.ChaCha20.X86.Stream.T s₀ = 0 then 0 else 1) := by
    rw [Proof.ChaCha20.X86.Xor.stateAt_frame hfw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ (by omega) (by omega)), h.state]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    all_goals simp (config := {decide := true}) only [ite_true, ite_false, h.esp]
  · exact hF.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.ret_st
      · exact hp.ret_d
      · exact VG.Proof.ChaCha20.X86.Stream.retR_stkR s₀ hp) (by decide)
  · have hd : ∀ k < VG.Proof.ChaCha20.X86.Stream.L s₀, ((s.mem.writeW (st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.N s₀ - VG.Proof.ChaCha20.X86.Stream.L s₀))).writeW
        (st s₀ + BitVec.ofNat 64 132) (BitVec.ofNat 32 ((VG.Proof.ChaCha20.X86.Stream.N s₀ - VG.Proof.ChaCha20.X86.Stream.L s₀) / 2 ^ 32)))
        (VG.Proof.ChaCha20.X86.Stream.dp s₀ + BitVec.ofNat 64 k) = s.mem (VG.Proof.ChaCha20.X86.Stream.dp s₀ + BitVec.ofNat 64 k) := fun k hk =>
      hfw.bytes (R := VG.Proof.ChaCha20.X86.Stream.dR s₀) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_d.symm.sub_right c128)) (show VG.Proof.ChaCha20.X86.Stream.L s₀ ≤ 2 ^ 64 by omega) hk
    show keyAt _ _ = _ ∧ _
    refine ⟨Proof.ChaCha20.keyAt_of_ctr hS, ?_⟩
    rw [ite_pos hle]
    refine ⟨by simp (config := {decide := true}), apply_data hle fun k hk => ?_,
      apply_rest hle ?_ hS fun i hi => ?_⟩
    · dsimp only
      rw [hd k hk, h.done k hk, ite_pos hk]
    · dsimp only
      rw [leftAt_halves _ _ (by omega)]
    · dsimp only
      rw [byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
        byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), h.buf i hi]

theorem apply_eq (v : Impl.ChaCha20.X86.Callee) : apply v = .seq (.block [.mov .eax (.mem (at_ .esp 4))])
    (.seq (.block check)
    (.ite .b (.block [.mov .eax (.imm 0)]) (.seq part1 (.seq (part2 v) (.seq part3 (.block finish)))))) := rfl

theorem apply_correct (v : XorImpl) {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) : WP isa (apply v.callee) s₀ (VG.Proof.ChaCha20.X86.Stream.Final s₀) := by
  rw [VG.Proof.ChaCha20.X86.Stream.apply_eq]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Stream.load_ok hp) fun s₁ e₁ => ?_)
  subst e₁
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Stream.check_ok hp) fun s h => ?_)
  refine WP.ite (decide (VG.Proof.ChaCha20.X86.Stream.N s₀ < VG.Proof.ChaCha20.X86.Stream.L s₀)) (by show eval .b s = _; simp only [eval, h.cf])
    (fun hlt => VG.Proof.ChaCha20.X86.Stream.fail_ok (by simpa using hlt) h) (fun hge => ?_)
  have hle : VG.Proof.ChaCha20.X86.Stream.L s₀ ≤ VG.Proof.ChaCha20.X86.Stream.N s₀ := by simp at hge; omega
  exact WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Stream.part1_ok hp hle h) fun s₁ h₁ => WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Stream.part2_ok v hp h₁) fun s₂ h₂ =>
    WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Stream.part3_ok hp h₂) fun s₃ h₃ => VG.Proof.ChaCha20.X86.Stream.finish_ok hp hle h₃)))

end VG.Proof.ChaCha20.X86.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.X86.Stream.ApplyCT`. -/
section

/-!
# Streaming ChaCha20 on x86 (32-bit): `apply`, constant time

Untrusted: everything here is checked by Lean. As on the other targets, two
runs from states that agree on `esp`, the arguments and the number of bytes
of keystream left (which the contract lets `apply` leak) are related piece
by piece (`RelCT`): the taint analysis proves each piece without calls
constant time from the registers that hold public values (`taintRel`), which
correctness determines in each run (`Apply.lean`) from those public values;
the calls of the block function and of `vg_chacha20_xor`, each in a frame of
its arguments, are constant time by their own proofs (`RelCT.callWith`),
their arguments agreeing; and the branches are on public values
(`RelCT.ite`). The argument slots may be written, so the taint analysis does
not take the arguments from them: the state pointer is loaded in a piece of
its own, whose result correctness determines.
-/

namespace VG.Proof.ChaCha20.X86.Stream

open VG VG.X86 VG.Impl.ChaCha20.X86.Stream
open VG.Impl.ChaCha20.X86 (at_)
open VG.Spec.ChaCha20 (stateAt)
open VG.Proof.ChaCha20.X86 (XorImpl)

/-- Code the taint analysis proves constant time from the registers `rs`. -/
theorem taintRel {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint sseTaint.T}
    (h : (sseTaint.check (τr rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := sseTaint) (τr rs) (fun x y hp => agree_regs (hr x y hp)) h

/-- What each run satisfies by correctness holds of the final states. -/
theorem RelCT.post {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop}
    (h : RelCT isa P c fun _ _ => True) (hw : ∀ x y, P x y → WP isa c x F₁ ∧ WP isa c y F₂) :
    RelCT isa P c fun x y => F₁ x ∧ F₂ y :=
  RelCT.mono (RelCT.wp h hw) (fun _ _ h => h) fun _ _ h => h.2

/-- Two entry states that agree on what is public. -/
structure Two (a b : State) : Prop where
  pa : VG.Proof.ChaCha20.X86.Stream.APre a
  pb : VG.Proof.ChaCha20.X86.Stream.APre b
  hesp : VG.Proof.ChaCha20.X86.Stream.E a = VG.Proof.ChaCha20.X86.Stream.E b
  hst : ST a = ST b
  hdp : VG.Proof.ChaCha20.X86.Stream.DP a = VG.Proof.ChaCha20.X86.Stream.DP b
  hln : VG.Proof.ChaCha20.X86.Stream.LN a = VG.Proof.ChaCha20.X86.Stream.LN b
  hleft : VG.Proof.ChaCha20.X86.Stream.N a = VG.Proof.ChaCha20.X86.Stream.N b

theorem Two.eqL {a b : State} (h : VG.Proof.ChaCha20.X86.Stream.Two a b) : VG.Proof.ChaCha20.X86.Stream.L a = VG.Proof.ChaCha20.X86.Stream.L b := by
  show (VG.Proof.ChaCha20.X86.Stream.LN a).toNat = (VG.Proof.ChaCha20.X86.Stream.LN b).toNat; rw [h.hln]
theorem Two.eqO {a b : State} (h : VG.Proof.ChaCha20.X86.Stream.Two a b) : VG.Proof.ChaCha20.X86.Stream.O a = VG.Proof.ChaCha20.X86.Stream.O b := by
  show VG.Proof.ChaCha20.X86.Stream.N a % 64 = VG.Proof.ChaCha20.X86.Stream.N b % 64; rw [h.hleft]
theorem Two.eqH {a b : State} (h : VG.Proof.ChaCha20.X86.Stream.Two a b) : VG.Proof.ChaCha20.X86.Stream.H a = VG.Proof.ChaCha20.X86.Stream.H b := by
  show min (VG.Proof.ChaCha20.X86.Stream.N a % 64) (VG.Proof.ChaCha20.X86.Stream.L a) = min (VG.Proof.ChaCha20.X86.Stream.N b % 64) (VG.Proof.ChaCha20.X86.Stream.L b); rw [h.hleft, h.eqL]
theorem Two.eqNB {a b : State} (h : VG.Proof.ChaCha20.X86.Stream.Two a b) : VG.Proof.ChaCha20.X86.Stream.NB a = VG.Proof.ChaCha20.X86.Stream.NB b := by
  show (VG.Proof.ChaCha20.X86.Stream.L a - VG.Proof.ChaCha20.X86.Stream.H a) / 64 = (VG.Proof.ChaCha20.X86.Stream.L b - VG.Proof.ChaCha20.X86.Stream.H b) / 64; rw [h.eqH, h.eqL]
theorem Two.eqT {a b : State} (h : VG.Proof.ChaCha20.X86.Stream.Two a b) : VG.Proof.ChaCha20.X86.Stream.T a = VG.Proof.ChaCha20.X86.Stream.T b := by
  show (VG.Proof.ChaCha20.X86.Stream.L a - VG.Proof.ChaCha20.X86.Stream.H a) % 64 = (VG.Proof.ChaCha20.X86.Stream.L b - VG.Proof.ChaCha20.X86.Stream.H b) % 64; rw [h.eqH, h.eqL]
theorem Two.st64 {a b : State} (h : VG.Proof.ChaCha20.X86.Stream.Two a b) : st a = st b := by simp only [st, h.hst]

/-- The callee's public data: `esp` and the arguments, which are the
registers pushed. -/
theorem entry_pub {rs : List Reg} {x y : State} (rd wr : List Region) (hrs : Reg.esp ∉ rs)
    (hfit : 4 * rs.length + 4 ≤ (x.gpr .esp).toNat) (hsp : x.gpr .esp = y.gpr .esp)
    (hr : ∀ r ∈ rs, x.gpr r = y.gpr r) :
    ((pushed rs x).callEntry.withRegions rd wr).gpr .esp = ((pushed rs y).callEntry.withRegions rd wr).gpr .esp ∧
    ∀ i < rs.length, arg ((pushed rs x).callEntry.withRegions rd wr) i =
      arg ((pushed rs y).callEntry.withRegions rd wr) i :=
  ⟨by simp only [State.withRegions_gpr, callEntry_esp', hsp],
   fun i hi => by simp only [arg_withRegions]; exact callEntry_arg_eq hrs hfit hsp hr hi⟩

/-- The arguments of the call of the block function, and the registers the
rest uses. -/
structure TArgs (s₀ s : State) : Prop where
  eax : s.gpr .eax = ST s₀ + BitVec.ofNat 32 64
  ebx : s.gpr .ebx = ST s₀
  esi : s.gpr .esi = VG.Proof.ChaCha20.X86.Stream.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.T s₀)
  at_ : VG.Proof.ChaCha20.X86.Stream.At s₀ s

theorem tailArgs_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20.X86.Stream.Q2 s₀ s) : WP isa (.block (ptr .eax .ebx 64)) s (VG.Proof.ChaCha20.X86.Stream.TArgs s₀) :=
  WP.mono (VG.Proof.ChaCha20.X86.Stream.tailPtr_ok h) fun _ ⟨eax₁, k₁, _, rd₁, wr₁⟩ =>
    ⟨eax₁, by rw [k₁ _ (by decide), h.ebx], by rw [k₁ _ (by decide), h.esi], by rw [k₁ _ (by decide), h.ebp],
      ⟨by rw [k₁ _ (by decide), h.esp], by rw [rd₁, h.rd], by rw [wr₁, h.wr]⟩⟩

/-- After the block function: the registers the rest uses. -/
structure TAfter (s₀ s : State) : Prop where
  ebx : s.gpr .ebx = ST s₀
  esi : s.gpr .esi = VG.Proof.ChaCha20.X86.Stream.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.H s₀ + 64 * VG.Proof.ChaCha20.X86.Stream.NB s₀)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Stream.T s₀)
  esp : s.gpr .esp = VG.Proof.ChaCha20.X86.Stream.E s₀

theorem TArgs.call {s₀ s : State} (hp : VG.Proof.ChaCha20.X86.Stream.APre s₀) (h : VG.Proof.ChaCha20.X86.Stream.TArgs s₀ s) : WP isa callBlock s (VG.Proof.ChaCha20.X86.Stream.TAfter s₀) :=
  VG.Proof.ChaCha20.X86.Stream.block_call hp h.at_ h.ebx h.eax fun _ at' cs _ _ =>
    ⟨by rw [cs .ebx (by simp [calleeSaved]), h.ebx], by rw [cs .esi (by simp [calleeSaved]), h.esi],
      by rw [cs .ebp (by simp [calleeSaved]), h.ebp], at'.esp⟩

section
variable {a b : State} (h : VG.Proof.ChaCha20.X86.Stream.Two a b)
include h

theorem load_rel : RelCT isa (fun x y => x = a ∧ y = b) (.block [.mov .eax (.mem (at_ .esp 4))])
    fun x y => x = a.setReg .eax (ST a) ∧ y = b.setReg .eax (ST b) :=
  RelCT.post (VG.Proof.ChaCha20.X86.Stream.taintRel [.esp] (fun x y ⟨hx, hy⟩ r hr => by
      subst hx hy
      simp only [List.mem_singleton] at hr; subst hr; exact h.hesp) (by taint_decide))
    fun x y ⟨hx, hy⟩ => ⟨by subst hx; exact VG.Proof.ChaCha20.X86.Stream.load_ok h.pa, by subst hy; exact VG.Proof.ChaCha20.X86.Stream.load_ok h.pb⟩

theorem check_rel : RelCT isa (fun x y => x = a.setReg .eax (ST a) ∧ y = b.setReg .eax (ST b)) (.block check)
    fun x y => VG.Proof.ChaCha20.X86.Stream.Q0 a x ∧ VG.Proof.ChaCha20.X86.Stream.Q0 b y :=
  RelCT.post (VG.Proof.ChaCha20.X86.Stream.taintRel [.eax, .esp] (fun x y ⟨hx, hy⟩ r hr => by
      subst hx hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [RegUpd.gpr_setReg_self, h.hst]
      · simp only [RegUpd.gpr_setReg_of_ne _ _ (show Reg.esp ≠ .eax by decide)]; exact h.hesp)
      (by taint_decide))
    fun x y ⟨hx, hy⟩ => ⟨by subst hx; exact VG.Proof.ChaCha20.X86.Stream.check_ok h.pa, by subst hy; exact VG.Proof.ChaCha20.X86.Stream.check_ok h.pb⟩

theorem part1_rel (hle : VG.Proof.ChaCha20.X86.Stream.L a ≤ VG.Proof.ChaCha20.X86.Stream.N a) :
    RelCT isa (fun x y => VG.Proof.ChaCha20.X86.Stream.Q0 a x ∧ VG.Proof.ChaCha20.X86.Stream.Q0 b y) part1 fun x y => VG.Proof.ChaCha20.X86.Stream.Q1 a x ∧ VG.Proof.ChaCha20.X86.Stream.Q1 b y := by
  have hle' : VG.Proof.ChaCha20.X86.Stream.L b ≤ VG.Proof.ChaCha20.X86.Stream.N b := by rw [← h.eqL, ← h.hleft]; exact hle
  rw [VG.Proof.ChaCha20.X86.Stream.part1_eq]
  refine RelCT.seq (R := fun (x y : State) => (VG.Proof.ChaCha20.X86.Stream.R1 a (VG.Proof.ChaCha20.X86.Stream.L a) x ∧ x.cf = some (decide (VG.Proof.ChaCha20.X86.Stream.O a < VG.Proof.ChaCha20.X86.Stream.L a))) ∧
      (VG.Proof.ChaCha20.X86.Stream.R1 b (VG.Proof.ChaCha20.X86.Stream.L b) y ∧ y.cf = some (decide (VG.Proof.ChaCha20.X86.Stream.O b < VG.Proof.ChaCha20.X86.Stream.L b))))
    (RelCT.post (VG.Proof.ChaCha20.X86.Stream.taintRel [.eax, .esp] (fun x y ⟨hx, hy⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hx.eax, hy.eax, h.hst]
        · rw [hx.keep _ (by decide) (by decide) (by decide), hy.keep _ (by decide) (by decide) (by decide)]
          exact h.hesp) (by taint_decide))
      fun x y ⟨hx, hy⟩ => ⟨VG.Proof.ChaCha20.X86.Stream.start_ok h.pa hle hx, VG.Proof.ChaCha20.X86.Stream.start_ok h.pb hle' hy⟩) ?_
  refine RelCT.seq (R := fun x y => VG.Proof.ChaCha20.X86.Stream.R1 a (VG.Proof.ChaCha20.X86.Stream.H a) x ∧ VG.Proof.ChaCha20.X86.Stream.R1 b (VG.Proof.ChaCha20.X86.Stream.H b) y)
    (RelCT.post (RelCT.ite (fun x y ⟨⟨_, cx⟩, ⟨_, cy⟩⟩ => by
        show eval .b x = eval .b y; simp only [eval, cx, cy, h.eqO, h.eqL])
      (VG.Proof.ChaCha20.X86.Stream.taintRel [] (fun _ _ _ r hr => by simp at hr) (by taint_decide))
      (VG.Proof.ChaCha20.X86.Stream.taintRel [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)))
      fun x y ⟨⟨hx, cx⟩, ⟨hy, cy⟩⟩ => ⟨VG.Proof.ChaCha20.X86.Stream.sel_ok hx cx, VG.Proof.ChaCha20.X86.Stream.sel_ok hy cy⟩) ?_
  exact RelCT.post (VG.Proof.ChaCha20.X86.Stream.taintRel [.ebx, .eax, .ecx, .esi, .ebp, .esp] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hx.ebx, hy.ebx, h.hst]
      · rw [hx.eax, hy.eax, h.eqO]
      · rw [hx.ecx, hy.ecx, h.eqH]
      · rw [hx.esi, hy.esi, h.hdp]
      · rw [hx.ebp, hy.ebp, h.hln]
      · rw [hx.esp, hy.esp, h.hesp]) (by taint_decide))
    fun x y ⟨hx, hy⟩ => ⟨VG.Proof.ChaCha20.X86.Stream.rest1_ok h.pa hx, VG.Proof.ChaCha20.X86.Stream.rest1_ok h.pb hy⟩

theorem xor_rel (v : XorImpl) (hnb : 0 < VG.Proof.ChaCha20.X86.Stream.NB a) :
    RelCT isa (fun x y => VG.Proof.ChaCha20.X86.Stream.Args a x ∧ VG.Proof.ChaCha20.X86.Stream.Args b y) (callXor v.callee) fun _ _ => True := by
  have ew : VG.Proof.ChaCha20.X86.Stream.wrXor b = VG.Proof.ChaCha20.X86.Stream.wrXor a := by
    simp only [VG.Proof.ChaCha20.X86.Stream.wrXor, VG.Proof.ChaCha20.X86.Stream.cpR, VG.Proof.ChaCha20.X86.Stream.blR, VG.Proof.ChaCha20.X86.Stream.wkR, st, VG.Proof.ChaCha20.X86.Stream.dp, VG.Proof.ChaCha20.X86.Stream.E, h.hst, h.hdp, h.eqH, h.eqNB, h.hesp]
  refine RelCT.callWith v.ok v.ct [] (VG.Proof.ChaCha20.X86.Stream.wrXor a)
    fun x y ⟨hx, hy⟩ => ?_
  have px := VG.Proof.ChaCha20.X86.Stream.xor_pre h.pa ⟨hx.esp, hx.rd, hx.wr⟩ hnb hx.edx hx.esi hx.ecx hx.eax
  have py := VG.Proof.ChaCha20.X86.Stream.xor_pre h.pb ⟨hy.esp, hy.rd, hy.wr⟩ (by rw [← h.eqNB]; exact hnb) hy.edx hy.esi hy.ecx hy.eax
  rw [ew] at py
  have fit := (At.fit h.pa ⟨hx.esp, hx.rd, hx.wr⟩ (rs := [.eax, .ecx, .esi, .edx]) (by decide))
  have hsp : x.gpr .esp = y.gpr .esp := by rw [hx.esp, hy.esp, h.hesp]
  have p := VG.Proof.ChaCha20.X86.Stream.entry_pub [] (VG.Proof.ChaCha20.X86.Stream.wrXor a) (by decide) fit hsp (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [hx.eax, hy.eax, h.hst]
    · rw [hx.ecx, hy.ecx, h.eqNB]
    · rw [hx.esi, hy.esi, h.hdp, h.eqH]
    · rw [hx.edx, hy.edx, h.hst])
  exact ⟨px, py, hsp, p.1, fun i hi => p.2 i hi⟩

theorem part2_rel (v : XorImpl) :
    RelCT isa (fun x y => VG.Proof.ChaCha20.X86.Stream.Q1 a x ∧ VG.Proof.ChaCha20.X86.Stream.Q1 b y) (part2 v.callee) fun x y => VG.Proof.ChaCha20.X86.Stream.Q2 a x ∧ VG.Proof.ChaCha20.X86.Stream.Q2 b y := by
  refine RelCT.post ?_ fun x y ⟨hx, hy⟩ => ⟨VG.Proof.ChaCha20.X86.Stream.part2_ok v h.pa hx, VG.Proof.ChaCha20.X86.Stream.part2_ok v h.pb hy⟩
  rw [VG.Proof.ChaCha20.X86.Stream.part2_eq]
  refine RelCT.ite (fun x y ⟨hx, hy⟩ => by show eval .e x = eval .e y; simp only [eval, hx.zf, hy.zf, h.eqNB])
    (VG.Proof.ChaCha20.X86.Stream.taintRel [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)) ?_
  by_cases h0 : 64 * VG.Proof.ChaCha20.X86.Stream.NB a = 0
  · exact RelCT.of_false fun x y ⟨⟨hx, _⟩, he⟩ => by
      simp only [show eval .e x = x.zf from rfl, hx.zf, h0, decide_true] at he
      exact absurd he (by decide)
  refine RelCT.seq (R := fun x y => VG.Proof.ChaCha20.X86.Stream.Args a x ∧ VG.Proof.ChaCha20.X86.Stream.Args b y) ?_
    (RelCT.seq (VG.Proof.ChaCha20.X86.Stream.xor_rel h v (by omega)) (VG.Proof.ChaCha20.X86.Stream.taintRel [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)))
  exact RelCT.post (VG.Proof.ChaCha20.X86.Stream.taintRel [.ebx, .ecx, .esp] (fun x y ⟨⟨hx, hy⟩, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hx.ebx, hy.ebx, h.hst]
      · rw [hx.ecx, hy.ecx, h.eqNB]
      · rw [hx.esp, hy.esp, h.hesp]) (by taint_decide))
    fun x y ⟨⟨hx, hy⟩, _⟩ => ⟨WP.mono (VG.Proof.ChaCha20.X86.Stream.args_exec h.pa hx) fun _ h' => h'.2, WP.mono (VG.Proof.ChaCha20.X86.Stream.args_exec h.pb hy) fun _ h' => h'.2⟩

theorem part3_rel : RelCT isa (fun x y => VG.Proof.ChaCha20.X86.Stream.Q2 a x ∧ VG.Proof.ChaCha20.X86.Stream.Q2 b y) part3 fun x y => VG.Proof.ChaCha20.X86.Stream.Q3 a x ∧ VG.Proof.ChaCha20.X86.Stream.Q3 b y := by
  refine RelCT.post ?_ fun x y ⟨hx, hy⟩ => ⟨VG.Proof.ChaCha20.X86.Stream.part3_ok h.pa hx, VG.Proof.ChaCha20.X86.Stream.part3_ok h.pb hy⟩
  rw [VG.Proof.ChaCha20.X86.Stream.part3_eq]
  refine RelCT.seq (R := fun (x y : State) => (VG.Proof.ChaCha20.X86.Stream.Q2 a x ∧ x.zf = some (decide (VG.Proof.ChaCha20.X86.Stream.T a = 0))) ∧
      (VG.Proof.ChaCha20.X86.Stream.Q2 b y ∧ y.zf = some (decide (VG.Proof.ChaCha20.X86.Stream.T b = 0))))
    (RelCT.post (VG.Proof.ChaCha20.X86.Stream.taintRel [] (fun _ _ _ r hr => by simp at hr) (by taint_decide))
      fun x y ⟨hx, hy⟩ => ⟨VG.Proof.ChaCha20.X86.Stream.test_ok hx, VG.Proof.ChaCha20.X86.Stream.test_ok hy⟩) ?_
  refine RelCT.ite (fun x y ⟨hx, hy⟩ => by show eval .e x = eval .e y; simp only [eval, hx.2, hy.2, h.eqT])
    (VG.Proof.ChaCha20.X86.Stream.taintRel [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)) ?_
  refine RelCT.seq (R := fun x y => VG.Proof.ChaCha20.X86.Stream.TArgs a x ∧ VG.Proof.ChaCha20.X86.Stream.TArgs b y)
    (RelCT.post (VG.Proof.ChaCha20.X86.Stream.taintRel [.ebx] (fun x y ⟨⟨hx, hy⟩, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hx.1.ebx, hy.1.ebx, h.hst]) (by taint_decide))
      fun x y ⟨⟨hx, hy⟩, _⟩ => ⟨VG.Proof.ChaCha20.X86.Stream.tailArgs_ok hx.1, VG.Proof.ChaCha20.X86.Stream.tailArgs_ok hy.1⟩) ?_
  refine RelCT.seq (R := fun x y => VG.Proof.ChaCha20.X86.Stream.TAfter a x ∧ VG.Proof.ChaCha20.X86.Stream.TAfter b y) ?_
    (VG.Proof.ChaCha20.X86.Stream.taintRel [.ebx, .esi, .ebp, .esp] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hx.ebx, hy.ebx, h.hst]
      · rw [hx.esi, hy.esi, h.hdp, h.eqH, h.eqNB]
      · rw [hx.ebp, hy.ebp, h.eqT]
      · rw [hx.esp, hy.esp, h.hesp]) (by taint_decide))
  have er : VG.Proof.ChaCha20.X86.Stream.rdBlk b = VG.Proof.ChaCha20.X86.Stream.rdBlk a := by simp only [VG.Proof.ChaCha20.X86.Stream.rdBlk, st, VG.Proof.ChaCha20.X86.Stream.E, h.hst, h.hesp]
  have ew : VG.Proof.ChaCha20.X86.Stream.wrBlk b = VG.Proof.ChaCha20.X86.Stream.wrBlk a := by simp only [VG.Proof.ChaCha20.X86.Stream.wrBlk, st, h.hst]
  refine RelCT.post (RelCT.callWith Proof.ChaCha20.X86.block_correct Proof.ChaCha20.X86.block_ct (VG.Proof.ChaCha20.X86.Stream.rdBlk a) (VG.Proof.ChaCha20.X86.Stream.wrBlk a)
    fun x y ⟨hx, hy⟩ => ?_) fun x y ⟨hx, hy⟩ => ⟨hx.call h.pa, hy.call h.pb⟩
  have py := VG.Proof.ChaCha20.X86.Stream.block_pre h.pb hy.at_ hy.ebx hy.eax
  rw [er, ew] at py
  have fit := hx.at_.fit h.pa (rs := [.eax, .ebx]) (by decide)
  have hsp : x.gpr .esp = y.gpr .esp := by rw [hx.at_.esp, hy.at_.esp, h.hesp]
  have p := VG.Proof.ChaCha20.X86.Stream.entry_pub (VG.Proof.ChaCha20.X86.Stream.rdBlk a) (VG.Proof.ChaCha20.X86.Stream.wrBlk a) (by decide) fit hsp (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hx.eax, hy.eax, h.hst]
    · rw [hx.ebx, hy.ebx, h.hst])
  exact ⟨VG.Proof.ChaCha20.X86.Stream.block_pre h.pa hx.at_ hx.ebx hx.eax, py, hsp, p.1, p.2 0 (by decide), p.2 1 (by decide)⟩

theorem apply_rel (v : XorImpl) : RelCT isa (fun x y => x = a ∧ y = b) (apply v.callee) fun _ _ => True := by
  rw [VG.Proof.ChaCha20.X86.Stream.apply_eq]
  refine RelCT.seq (VG.Proof.ChaCha20.X86.Stream.load_rel h) (RelCT.seq (VG.Proof.ChaCha20.X86.Stream.check_rel h) (RelCT.ite (fun x y ⟨hx, hy⟩ => by
      show eval .b x = eval .b y; simp only [eval, hx.cf, hy.cf, h.hleft, h.eqL])
    (VG.Proof.ChaCha20.X86.Stream.taintRel [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)) ?_))
  by_cases hlt : VG.Proof.ChaCha20.X86.Stream.N a < VG.Proof.ChaCha20.X86.Stream.L a
  · exact RelCT.of_false fun x y ⟨⟨hx, _⟩, he⟩ => by
      simp only [show eval .b x = x.cf from rfl, hx.cf, hlt, decide_true] at he
      exact absurd he (by decide)
  have hle : VG.Proof.ChaCha20.X86.Stream.L a ≤ VG.Proof.ChaCha20.X86.Stream.N a := by omega
  refine RelCT.seq (RelCT.mono (VG.Proof.ChaCha20.X86.Stream.part1_rel h hle) (fun _ _ hp => hp.1) fun _ _ hq => hq)
    (RelCT.seq (VG.Proof.ChaCha20.X86.Stream.part2_rel h v) (RelCT.seq (VG.Proof.ChaCha20.X86.Stream.part3_rel h) ?_))
  exact VG.Proof.ChaCha20.X86.Stream.taintRel [.ebx] (fun x y ⟨hx, hy⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [hx.ebx, hy.ebx, h.hst]) (by taint_decide)

end

theorem Two.of {a b : State} (ha : Proof.ChaCha20.applyX86.pre a) (hb : Proof.ChaCha20.applyX86.pre b)
    (hq : Proof.ChaCha20.applyX86.pub a b) : VG.Proof.ChaCha20.X86.Stream.Two a b := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hq
  exact ⟨APre.of a ha, APre.of b hb, p1, p2, p3, p4, (List.cons.inj p5).1⟩

theorem apply_ct (v : XorImpl) :
    ConstantTime isa Proof.ChaCha20.applyX86.pre Proof.ChaCha20.applyX86.pub (apply v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.ChaCha20.X86.Stream.apply_rel (Two.of h₁ h₂ hq) v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem apply_ok (v : XorImpl) (s : State) (hs : Proof.ChaCha20.applyX86.pre s) :
    ∃ t s', Exec isa (apply v.callee) s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.applyX86.post s s' := by
  obtain ⟨t, s', he, hf⟩ := VG.Proof.ChaCha20.X86.Stream.apply_correct v (APre.of s hs)
  exact ⟨t, s', he, hf.1, hf.2⟩

/-- The 32-bit result, as the ABI returns it in `edx:eax`. -/
theorem ret_eq (x y : BitVec 32) : (x ++ y).setWidth 32 = y := by
  ext i hi
  rw [BitVec.getElem_setWidth, BitVec.getLsbD_append, ite_pos hi, BitVec.getLsbD_eq_getElem hi]

/-- Memory whose argument slots (at `0x4004`) hold `0x1000`, `0x2000` and 0. -/
def applySatMem : Mem := fun a => if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else 0

/-- A state satisfying the precondition of `apply` (with no data). -/
def applySat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.ChaCha20.X86.Stream.applySatMem
  rd := []
  wr := [⟨0x1000, 768⟩, ⟨0x2000, 0⟩, ⟨0x4004, 12⟩]

theorem apply_verified (v : XorImpl) :
    Verified X86.target (apply v.callee) (Spec.ChaCha20.applyContract X86.abi 32) :=
  Verified.of_correct (VG.Proof.ChaCha20.X86.Stream.apply_ok v) (VG.Proof.ChaCha20.X86.Stream.apply_ct v) (by
    have a0 : arg VG.Proof.ChaCha20.X86.Stream.applySat 0 = 0x1000 := by decide
    have a1 : arg VG.Proof.ChaCha20.X86.Stream.applySat 1 = 0x2000 := by decide
    have a2 : arg VG.Proof.ChaCha20.X86.Stream.applySat 2 = 0 := by decide
    have e : argAddr VG.Proof.ChaCha20.X86.Stream.applySat 0 = 0x4004 := by decide
    have esp : applySat.gpr .esp = 0x4000 := rfl
    sig_implies [Spec.ChaCha20.applyContract, Spec.ChaCha20.applySig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, Proof.ChaCha20.applyX86, VG.Proof.ChaCha20.X86.Stream.ret_eq] [a0, a1, a2, e, esp] using VG.Proof.ChaCha20.X86.Stream.applySat)

theorem apply_spSafe (v : XorImpl) : (apply v.callee).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [apply, part2, callXor, Code.all, v.spSafe, Bool.and_true]
  lit_decide

end VG.Proof.ChaCha20.X86.Stream

end
