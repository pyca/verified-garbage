module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Final
public import VerifiedGarbage.Proof.Mont.X86.Sse2.Mcdt
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath
import VerifiedGarbage.Proof.Mont.X86.Sse2.Columns
import Mathlib.Util.CompileInductive

/-! # The kernel

The columns in an MCDT frame, whose two words lie below the parameters and
apart from the working space, then the reduction (`kernel_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Mont.X86.Dynamic (ArgFar)

/-- The parameters read the same in a state `t` whose reads of them are the
same bytes, holding the same values, with the same permissions. -/
theorem Params.transport {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {d d' : Nat}
    (P : Params s W L V d) (hea : ∀ i < 7, t.ea (prm d' i) = s.ea (prm d i))
    (hmem : ∀ i < 7, ∀ j < 4, t.mem (s.ea (prm d i) + BitVec.ofNat 64 j) = s.mem (s.ea (prm d i) + BitVec.ofNat 64 j))
    (hrw : ∀ a, InRegions (s.rd ++ s.wr) a 4 → InRegions (t.rd ++ t.wr) a 4) : Params t W L V d' := by
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
  · have h := P.read i hi
    show t.load32 (t.ea (prm d' i)) = _
    change s.load32 (s.ea (prm d i)) = _ at h
    rw [hea i hi]
    simp only [State.load32] at h ⊢
    split at h
    · rename_i hr
      rw [ite_eq_left (hrw _ hr), ← h, Mem.readW_congr fun j hj => hmem i hi j hj]
    · cases h
  · rw [hea i hi]; exact P.far i hi j hj

/-- The offset of a byte of the parameters from the MCDT frame's bottom. -/
theorem ofs_param {sp : BitVec 32} (hlo : 12 ≤ sp.toNat) (hhi : sp.toNat + 28 ≤ 2 ^ 32) {i j : Nat} (hi : i < 7)
    (hj : j < 4) :
    ofs ((sp - 12).setWidth 64) ((sp + BitVec.ofNat 32 (0 + 4 * i)).setWidth 64 + BitVec.ofNat 64 j) =
      12 + 4 * i + j := by
  simp only [ofs, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show (12 : BitVec 32).toNat = 12 from rfl]
  omega_arith

/-- The MCDT frame's push writes no byte of the parameters. -/
theorem pushed_param (s : State) (hlo : 12 ≤ (s.gpr .esp).toNat) (hhi : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32)
    {i j : Nat} (hi : i < 7) (hj : j < 4) :
    (mcdtPushed .eax s).mem (s.ea (prm 0 i) + BitVec.ofNat 64 j) = s.mem (s.ea (prm 0 i) + BitVec.ofNat 64 j) := by
  have b0 : ((s.gpr .esp - 12).setWidth 64 : Addr) = off ((s.gpr .esp - 12).setWidth 64) 0 := by
    simp only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  have b4 : ((s.gpr .esp - 8).setWidth 64 : Addr) = off ((s.gpr .esp - 12).setWidth 64) 4 := by
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .esp).isLt
    simp only [off, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [show (12 : BitVec 32).toNat = 12 from rfl, show (8 : BitVec 32).toNat = 8 from rfl]
    omega_arith
  have o := ofs_param hlo hhi hi hj
  simp only [mcdtPushed]
  rw [b0, b4]
  rw [writeW32_outside _ _ _ (by decide) _ (by simp only [State.ea, prm, at_] at o ⊢; omega_arith),
    writeW32_outside _ _ _ (by decide) _ (by simp only [State.ea, prm, at_] at o ⊢; omega_arith)]

/-- The MCDT frame's push writes only its 8 bytes. -/
theorem pushed_other (s : State) (hlo : 12 ≤ (s.gpr .esp).toNat) {x : Addr}
    (hx : ∀ j < 8, x ≠ (s.gpr .esp - 12).setWidth 64 + BitVec.ofNat 64 j) :
    (mcdtPushed .eax s).mem x = s.mem x := by
  have b4 : ((s.gpr .esp - 8).setWidth 64 : Addr) = (s.gpr .esp - 12).setWidth 64 + BitVec.ofNat 64 4 := by
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .esp).isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [show (12 : BitVec 32).toNat = 12 from rfl, show (8 : BitVec 32).toNat = 8 from rfl]
    omega_arith
  simp only [mcdtPushed, Mem.writeW]
  rw [Mem.write_apply (fun h => hx ((x - (s.gpr .esp - 12).setWidth 64).toNat) (by omega_arith)
      (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel])),
    Mem.write_apply (fun h => hx ((x - (s.gpr .esp - 12).setWidth 64).toNat) (by
      rw [b4] at h
      have := (Offset.lt_iff x ((s.gpr .esp - 12).setWidth 64) (d := 4) (n := 4) (by decide)).mp h
      omega_arith) (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]))]

/-- The MCDT frame's push writes no byte of the working space. -/
theorem pushed_ws (s : State) {W : Addr} {L : Nat}
    (hfar : ∀ j < 8, L ≤ ofs W ((s.gpr .esp - 12).setWidth 64 + BitVec.ofNat 64 j))
    (hlo : 12 ≤ (s.gpr .esp).toNat) : Outs W [(L, 2 ^ 64)] s.mem (mcdtPushed .eax s).mem := by
  intro x hx
  have hx' : ofs W x < L := by
    have := hx _ (List.mem_singleton_self _)
    have : ofs W x < 2 ^ 64 := (x - W).isLt
    simp only at *; omega_arith
  exact pushed_other s hlo fun j hj h => by have := hfar j hj; rw [← h] at this; omega_arith

theorem value_digits (m : Mem) (W : Addr) (x n : Nat) :
    Column.value (2 ^ 32) (digits m W x) n = val32 m W x n := VG.Proof.Mont.X86.Square.value_val32 m W x n

theorem columns_noSp' : NoSp columns := NoSp.of_all (by decide +kernel)

/-- What the kernel takes of its entry state: the layout, the parameters `V`
in its frame at `esp`, and the 40 bytes from 12 below `esp` (the MCDT
frame's and the parameters') past the working space. -/
structure KReady (s : State) (W : Addr) (L N S mo inv o a b : Nat) (V : Nat → BitVec 32) : Prop where
  ly : Lay L N S mo inv o a b
  pv : PVals V W N S mo inv o a b
  ws : Ws s W L
  prm : Params s W L V 0
  lo : 12 ≤ (s.gpr .esp).toNat
  hi : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  far : ∀ j < 40, L ≤ ofs W ((s.gpr .esp - 12).setWidth 64 + BitVec.ofNat 64 j)
  inv : (w32 s.mem W mo * w32 s.mem W inv + 1) % 2 ^ 32 = 0
  bLt : val32 s.mem W b N < val32 s.mem W mo N

section
variable {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b : Nat}

/-- The columns' entry, inside the MCDT frame: the working space as it was,
the parameters 12 bytes above `esp`. -/
theorem pushed_ready (K : KReady s W L N S mo inv o a b V) :
    Ws (mcdtPushed .eax s) W L ∧ Params (mcdtPushed .eax s) W L V 12 ∧
    (w32 (mcdtPushed .eax s).mem W mo * w32 (mcdtPushed .eax s).mem W inv + 1) % 2 ^ 32 = 0 ∧
    ∀ {d k : Nat}, d + 4 * k ≤ L → val32 (mcdtPushed .eax s).mem W d k = val32 s.mem W d k := by
  have hn := K.ws.nowrap
  have Ly := K.ly
  have esp0 : (mcdtPushed .eax s).gpr .esp = s.gpr .esp - 12 := mcdtPushed_esp _ _ (by decide)
  have O0 := pushed_ws s (fun j hj => K.far j (by omega_arith)) K.lo
  have ws0 : ∀ {d k : Nat}, d + 4 * k ≤ L → val32 (mcdtPushed .eax s).mem W d k = val32 s.mem W d k := fun hd =>
    O0.val32 (by simp only [List.mem_singleton, forall_eq]; omega_arith) (by omega_arith)
  refine ⟨⟨List.mem_cons_of_mem _ K.ws.wr, hn⟩, K.prm.transport
    (fun i _ => by
      simp only [State.ea, prm, at_, esp0]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
      rw [show (12 : BitVec 32).toNat = 12 from rfl]
      omega_arith)
    (fun i hi j hj => pushed_param s K.lo K.hi hi hj)
    (fun a ⟨r, hr, hc⟩ => ⟨r, by
      rcases List.mem_append.mp hr with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h), hc⟩), ?_, ws0⟩
  have e1 := ws0 (d := mo) (k := 1) (by have := Ly.mo_le; have := Ly.hN; omega_arith)
  have e2 := ws0 (d := inv) (k := 1) (by have := Ly.inv_le; omega_arith)
  simp only [val32, Nat.mul_zero, Nat.add_zero] at e1 e2
  rw [e1, e2]; exact K.inv

/-- The value of `N` digits below `2³²`. -/
theorem value_lt_pow {q : Nat → Nat} (hq : ∀ i, q i ≤ 2 ^ 32 - 1) :
    ∀ N, Column.value (2 ^ 32) q N < 2 ^ (32 * N)
  | 0 => by simp [Column.value]
  | N + 1 => by
    have ih := value_lt_pow hq N
    have hN := hq N
    simp only [Column.value, NatSum.succ] at ih ⊢
    rw [← Nat.pow_mul, pow32_succ]
    generalize hX : 2 ^ (32 * N) = X at ih ⊢
    have := Nat.mul_le_mul_right X hN
    rw [Nat.sub_mul, Nat.one_mul] at this
    omega_arith

/-- After the MCDT frame: `R (T + R c) = A B + Q M` for some `Q` (the
quotient digits'), with `T + R c < 2 M`, `T`'s words in reverse at `S + 24`;
the memory as it was but the scratch and the MCDT frame's 8 bytes; `esp` and
the permissions as they were. -/
structure Mid (s : State) (W : Addr) (L N S mo inv o a b : Nat) (V : Nat → BitVec 32) (v : State) : Prop where
  ws : Ws v W L
  prm : Params v W L V 0
  esp : v.gpr .esp = s.gpr .esp
  rd : v.rd = s.rd
  wr : v.wr = s.wr
  modulus : val32 v.mem W mo N = val32 s.mem W mo N
  bound : rvalT v.mem W N S N + 2 ^ (32 * N) * w32 v.mem W (S + 16) < 2 * val32 s.mem W mo N
  eqn : ∃ Q, 2 ^ (32 * N) * (rvalT v.mem W N S N + 2 ^ (32 * N) * w32 v.mem W (S + 16)) =
    val32 s.mem W a N * val32 s.mem W b N + Q * val32 s.mem W mo N
  out : ∀ x, (∀ j < 8, x ≠ (s.gpr .esp - 12).setWidth 64 + BitVec.ofNat 64 j) →
    (ofs W x < S ∨ S + (8 * N + 28) ≤ ofs W x) → v.mem x = s.mem x

/-- The columns in their MCDT frame. -/
theorem frame_ok (K : KReady s W L N S mo inv o a b V) :
    WP isa (.frame (.mcdtEnter .eax) columns .mcdtLeave) s (Mid s W L N S mo inv o a b V) := by
  have Ly := K.ly
  have hn := K.ws.nowrap
  have hs := Ly.s_le
  have hN := Ly.hN
  have hlo := K.lo
  have hhi := K.hi
  let s0 := mcdtPushed .eax s
  have esp0 : s0.gpr .esp = s.gpr .esp - 12 := mcdtPushed_esp _ _ (by decide)
  obtain ⟨hw0, P0, hinv0, ws0⟩ := pushed_ready K
  refine WP.mcdtFrame (by decide) hlo columns_noSp'
    (WP.mono (columns_ok Ly K.pv hinv0 (by rw [mcdtPushed_mcdt]; omega_arith) hw0 P0) fun u ⟨c, q, I⟩ => ?_)
  have Ku := I.keep
  have espu : u.gpr .esp = s0.gpr .esp := Ku.1 _ (by decide)
  -- Memory past the working space, as the push left it.
  have far : ∀ x, L ≤ ofs W x → u.mem x = s0.mem x := fun x hx =>
    I.out x (by simp only [List.mem_singleton, forall_eq]; omega_arith)
  refine ⟨by rw [I.mcdt, mcdtPushed_mcdt], ?_, ?_⟩
  · rw [espu, ← mcdtPushed_saved .eax s (by decide) hlo]
    refine Mem.readW_congr fun j hj => far _ ?_
    have e : (s0.gpr .esp + 4).setWidth 64 + BitVec.ofNat 64 j =
        (s.gpr .esp - 12).setWidth 64 + BitVec.ofNat 64 (4 + j) := by
      rw [esp0]
      apply BitVec.eq_of_toNat_eq
      have := (s.gpr .esp).isLt
      simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
      rw [show (12 : BitVec 32).toNat = 12 from rfl, show (4 : BitVec 32).toNat = 4 from rfl]
      omega_arith
    rw [e]; exact K.far _ (by omega_arith)
  -- After the frame.
  have hpe : (mcdtPopped u).gpr .esp = s.gpr .esp := by
    rw [mcdtPopped_esp, espu, esp0, BitVec.sub_add_cancel]
  have hpw : (mcdtPopped u).wr = s.wr := by rw [mcdtPopped_wr, Ku.2.2]; rfl
  have hpr : (mcdtPopped u).rd = s.rd := by rw [mcdtPopped_rd, Ku.2.1]; rfl
  -- The columns' equation, at the end.
  have eq := I.eq
  rw [show 2 * N - N = N by omega_arith] at eq
  rw [Column.partSum_done _ _ _ (Nat.le_refl _), Column.partSum_congr_left _ _ N (2 * N)
    (b := q) (fun i hi => by simp only [Column.prefixDigits]; rw [ite_eq_left (by omega_arith)]),
    Column.partSum_done _ _ _ (Nat.le_refl _)] at eq
  simp only [value_digits] at eq
  have ea := ws0 (d := a) (k := N) Ly.a_le
  have eb := ws0 (d := b) (k := N) Ly.b_le
  have em := ws0 (d := mo) (k := N) Ly.mo_le
  rw [ea, eb, em, VG.Proof.Mont.X86.Square.pow32, VG.Proof.Mont.X86.Square.pow32, show (2 : Nat) ^ (32 * (2 * N)) = 2 ^ (32 * N) * 2 ^ (32 * N) by
    rw [← Nat.pow_add]; congr 1; omega_arith] at eq
  have eq' : 2 ^ (32 * N) * (rvalT u.mem W N S N + 2 ^ (32 * N) * c) =
      val32 s.mem W a N * val32 s.mem W b N + Column.value (2 ^ 32) q N * val32 s.mem W mo N := by
    rw [← eq]; grind
  obtain ⟨hT, hc2⟩ := final_bound (val32_lt _ _ _ _) K.bLt (Nat.le_of_lt (val32_lt _ _ _ _))
    (value_lt_pow I.qlt N) eq'
  have hc0 : w32 u.mem W (S + 16) = c := by
    have := I.carry
    have := Nat.zero_le (w32 u.mem W (S + 20))
    have : w32 u.mem W (S + 20) = 0 := by
      rcases Nat.eq_zero_or_pos (w32 u.mem W (S + 20)) with h | h
      · exact h
      · have : 2 ^ 32 ≤ 2 ^ 32 * w32 u.mem W (S + 20) := Nat.le_mul_of_pos_right _ h
        omega_arith
    omega_arith
  have mou : val32 u.mem W mo N = val32 s.mem W mo N := by
    rw [← em]; exact I.out.val32 (by have := Ly.smo; simp only [List.mem_singleton, forall_eq]; omega_arith)
      (by have := Ly.mo_le; omega_arith)
  refine ⟨⟨by rw [hpw]; exact K.ws.wr, hn⟩, K.prm.transport
    (fun i _ => by simp only [State.ea, prm, at_, hpe])
    (fun i hi j hj => by
      rw [mcdtPopped_mem, far _ (K.prm.far i hi j hj)]; exact pushed_param s hlo hhi hi hj)
    (fun a h => by rw [hpr, hpw]; exact h), hpe, hpr, hpw, by rw [mcdtPopped_mem, mou],
    by rw [mcdtPopped_mem, hc0]; exact hT, ⟨_, by rw [mcdtPopped_mem, hc0]; exact eq'⟩, fun x hx hr => ?_⟩
  rw [mcdtPopped_mem, I.out x (fun r h => by simp only [List.mem_singleton] at h; subst h; exact hr),
    pushed_other s hlo hx]

/-- The kernel: `O = A B R⁻¹ mod M`; only the scratch, `O` and memory past
the working space (the MCDT frame's bytes) change, and every register but
`esp` may. -/
theorem kernel_ok (K : KReady s W L N S mo inv o a b V) :
    WP isa kernel s fun v =>
      val32 v.mem W o N < val32 s.mem W mo N ∧
      val32 v.mem W o N * 2 ^ (32 * N) % val32 s.mem W mo N =
        val32 s.mem W a N * val32 s.mem W b N % val32 s.mem W mo N ∧
      (∀ x, (∀ j < 8, x ≠ (s.gpr .esp - 12).setWidth 64 + BitVec.ofNat 64 j) →
        (∀ r ∈ [(S, 8 * N + 28), (o, 4 * N)], ofs W x < r.1 ∨ r.1 + r.2 ≤ ofs W x) → v.mem x = s.mem x) ∧
      Keeps clob7 s v := by
  have Ly := K.ly
  have hs := Ly.s_le
  have hN := Ly.hN
  have hn := K.ws.nowrap
  simp only [kernel, seqs]
  refine WP.seq (WP.mono (frame_ok K) fun p M => WP.mono
    (reduction_ok Ly K.pv M.ws M.prm (by rw [M.modulus]; exact M.bound)) fun v ⟨Vv, Ov, Kv⟩ => ?_)
  have hM : 0 < val32 s.mem W mo N := by have := K.bLt; omega_arith
  rw [M.modulus] at Vv
  obtain ⟨Q, eqn⟩ := M.eqn
  refine ⟨by rw [Vv]; exact Nat.mod_lt _ hM, by rw [Vv]; exact final_mod eqn, ?_, ?_⟩
  · intro x hx hr
    have h1 : v.mem x = p.mem x :=
      Ov x fun r h => by
        have h0 := hr _ (List.mem_cons_self ..)
        have h2 := hr _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h h0 h2
        rcases h with rfl | rfl
        · simp only; omega_using [h0]
        · simp only; omega_using [h2]
    rw [h1, M.out x hx (hr _ (List.mem_cons_self ..))]
  · refine ⟨fun r hr => ?_, by rw [Kv.2.1, M.rd], by rw [Kv.2.2, M.wr]⟩
    cases r <;> simp only [clob7, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false, or_true, not_true_eq_false]
      at hr
    rw [Kv.1 _ (by decide), M.esp]

end

end VG.Proof.Mont.X86.Sse2
