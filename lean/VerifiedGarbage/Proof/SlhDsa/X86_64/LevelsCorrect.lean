module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
public import VerifiedGarbage.Proof.SlhDsa.X86_64.Contracts
public import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4Impl
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.SlhDsa.Lemmas

/-!
# SLH-DSA (SHAKE) on x86-64: `levels`, correctness

From a state satisfying `levelsContract`'s precondition (`σ`), `levels`
ends with the node of the top height first at `nodes`, and each node of the
authentication path XORed in (`correct`). The proof follows the code: the
prologue, the loop of heights with the invariant `HI` (one height: the scan
of the nodes, `Scan`, then the groups of four `H`s, `Lvl`), and the
epilogue.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Levels

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout savedRegs)
open VG.Impl.SlhDsa.X86_64.Tree

/-! ## The heights, one at a time -/

section Spec
variable (p : Params) (pkSeed a16 : List Byte) (ty kp base : Nat)

/-- The nodes of height `z + 1` from those `L` of height `z`. -/
def step (z : Nat) (L : List (List Byte)) : List (List Byte) :=
  (List.range (L.length / 2)).map fun j =>
    H p pkSeed (nodeAdrs a16 ty kp (z + 1) (base / 2 ^ (z + 1) + j)) (L.getD (2 * j) [] ++ L.getD (2 * j + 1) [])

theorem upNodes_succ : ∀ (r z : Nat) (L : List (List Byte)),
    upNodes p pkSeed a16 ty kp base z L (r + 1) = step p pkSeed a16 ty kp base (z + r) (upNodes p pkSeed a16 ty kp base z L r)
  | 0, z, L => by simp [upNodes, step]
  | r + 1, z, L => by
    rw [upNodes, upNodes_succ r (z + 1), upNodes, show z + 1 + r = z + (r + 1) by omega_using []]

theorem length_step (z : Nat) (L : List (List Byte)) : (step p pkSeed a16 ty kp base z L).length = L.length / 2 := by
  simp [step]

theorem length_upNodes : ∀ (r z : Nat) (L : List (List Byte)),
    (upNodes p pkSeed a16 ty kp base z L r).length = L.length / 2 ^ r
  | 0, _, _ => by simp [upNodes]
  | r + 1, z, L => by
    rw [upNodes_succ, length_step, length_upNodes r, Nat.pow_succ, Nat.div_div_eq_div_mul]

theorem getD_step (z : Nat) (L : List (List Byte)) {j : Nat} (hj : j < L.length / 2) :
    (step p pkSeed a16 ty kp base z L).getD j [] =
      H p pkSeed (nodeAdrs a16 ty kp (z + 1) (base / 2 ^ (z + 1) + j)) (L.getD (2 * j) [] ++ L.getD (2 * j + 1) []) := by
  simp [step, List.getD_eq_getElem?_getD, hj]

end Spec

/-! ## Bytes -/

/-- Byte `i` of `bytesAt`. -/
theorem getD_bytesAt (m : Mem) (a : Addr) {L i : Nat} (hi : i < L) : (bytesAt m a L).getD i 0 = m (a + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

/-- The `L` bytes at `a` are `l` if each is. -/
theorem bytesAt_eq {m : Mem} {a : Addr} {L : Nat} {l : List Byte} (hl : l.length = L)
    (h : ∀ i < L, m (a + BitVec.ofNat 64 i) = l.getD i 0) : bytesAt m a L = l :=
  Proof.SlhDsa.ext_getD (by simp [bytesAt, hl]) fun i hi => by
    simp only [bytesAt, List.length_map, List.length_range] at hi
    rw [getD_bytesAt _ _ hi, h i hi]

theorem length_nodeAdrs {a16 : List Byte} (ha : a16.length = 16) (ty kp z j : Nat) :
    (nodeAdrs a16 ty kp z j).length = 32 := by
  have h32 : (treeAdrs a16).length = 32 := by simp [treeAdrs, ha, Proof.SlhDsa.length_toByte]
  simp only [nodeAdrs]
  rw [Proof.SlhDsa.length_setTreeIndex (Proof.SlhDsa.length_setTreeHeight (Proof.SlhDsa.length_setKeyPairAddress
    (Proof.SlhDsa.length_setTypeAndClear h32 _) _) _)]

/-- The bytes of a node's address: the tree's 16, then the type, the key pair,
the height and the index, big-endian. -/
theorem getD_nodeAdrs {a16 : List Byte} (ha : a16.length = 16) (ty kp z j i : Nat) (hi : i < 32) :
    (nodeAdrs a16 ty kp z j).getD i 0 =
      if i < 16 then a16.getD i 0 else if i < 20 then (toByte ty 4).getD (i - 16) 0
      else if i < 24 then (toByte kp 4).getD (i - 20) 0 else if i < 28 then (toByte z 4).getD (i - 24) 0
      else (toByte j 4).getD (i - 28) 0 := by
  have h32 : (treeAdrs a16).length = 32 := by simp [treeAdrs, ha, Proof.SlhDsa.length_toByte]
  have l1 := Proof.SlhDsa.length_setTypeAndClear h32 ty
  have l2 := Proof.SlhDsa.length_setKeyPairAddress l1 kp
  have l3 := Proof.SlhDsa.length_setTreeHeight l2 z
  simp only [nodeAdrs]
  rw [Proof.SlhDsa.getD_setTreeIndex l3, Proof.SlhDsa.getD_setTreeHeight l2, Proof.SlhDsa.getD_setKeyPairAddress l1,
    Proof.SlhDsa.getD_setTypeAndClear h32]
  have ht : ∀ k < 16, (treeAdrs a16).getD k 0 = a16.getD k 0 := fun k hk => by
    rw [treeAdrs, Proof.SlhDsa.getD_append, ite_eq_left (by rw [ha]; exact hk)]
  rcases (show i < 16 ∨ (16 ≤ i ∧ i < 20) ∨ (20 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 28) ∨ (28 ≤ i ∧ i < 32)
    by omega_using [hi]) with hr | hr | hr | hr | hr
  · simp (disch := omega_using [hr]) only [↓ite_eq_left]; exact ht i hr
  · simp (disch := omega_using [hr]) only [↓ite_eq_left, ↓ite_eq_right]
  · simp (disch := omega_using [hr]) only [↓ite_eq_left, ↓ite_eq_right]
  · simp (disch := omega_using [hr]) only [↓ite_eq_left, ↓ite_eq_right]
  · simp (disch := omega_using [hr]) only [↓ite_eq_left, ↓ite_eq_right]

/-- `H` for the SHAKE parameter sets: SHAKE256 of `PK.seed ‖ ADRS ‖ M`. -/
theorem H_shake {p : Params} (hf : p.family = .shake) (pk : List Byte) (a : Adrs) (M : List Byte) :
    H p pk a M = Spec.Sha3.shake256 (pk ++ a ++ M) p.n := by
  simp only [H, hf, shakeAdrs]

/-! ## The entry state -/

variable (p : Params) (σ : State)

/-- `scratch`, the number of nodes, the first height, the authentication
path and `idx`, at the entry state. -/
abbrev Sb : Addr := σ.gpr .rdi
abbrev Cn : Nat := (σ.gpr .rdx).toNat
abbrev Z0 : Nat := (σ.gpr .rcx).toNat
abbrev AU : Addr := σ.gpr .r8
abbrev hgt : Nat := heightsOf σ

/-- The parameters in frame 4. -/
abbrev capB : Nat := (varAt σ.mem (Sb σ) 4 5).toNat
abbrev baseA : Nat := (varAt σ.mem (Sb σ) 4 6).toNat
abbrev tyA : Nat := (varAt σ.mem (Sb σ) 4 7).toNat
abbrev kpA : Nat := (varAt σ.mem (Sb σ) 4 8).toNat

/-- The nodes at the entry state, and those of height `Z0 + r` above them. -/
abbrev L0 : List (List Byte) := nodesAt p σ.mem (σ.gpr .rsi) (Cn σ)
abbrev up (pkSeed a16 : List Byte) (r : Nat) : List (List Byte) :=
  upNodes p pkSeed a16 (tyA σ) (kpA σ) (baseA σ) (Z0 σ) (L0 p σ) r

/-- The authentication path's node `r` at the entry state. -/
abbrev oldAuth (r : Nat) : List Byte := bytesAt σ.mem (AU σ + BitVec.ofNat 64 (r * p.n)) p.n

/-- What the proof uses of the precondition: the nodes are `no` bytes into
`scratch`, below `oSigTmp`, the `n` of a SHAKE parameter set. -/
structure Ctx (stack : Nat) (no : Nat) : Prop where
  reg : Regions stack σ (Sb σ) [] ⟨AU σ, hgt σ * p.n⟩
  np : σ.gpr .rsi = at' (Sb σ) no
  no_lo : 3808 ≤ no
  no_hi : no + (Cn σ + 8) * p.n ≤ Layout.oSigTmp
  h_pos : 1 ≤ hgt σ
  h_le : Z0 σ + hgt σ ≤ 14
  cnt : Cn σ = 2 ^ hgt σ
  idx_lt : (σ.gpr .r9).toNat < 2 ^ 32
  cap_lt : capB σ < 2 ^ 32
  base_lt : baseA σ < 2 ^ 32
  n_eq : p.n = 16 ∨ p.n = 24 ∨ p.n = 32

theorem ctx_of {stack : Nat} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (h : (levelsContract p stack).pre σ) :
    ∃ no, Ctx p σ stack no := by
  obtain ⟨hr, _, hnp, h1, h2, h3, h4, h5, h6, h7, h8, _, _⟩ := h
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have e1 : Layout.oN = 12640 := rfl
  have e2 : Layout.oRoots = 29280 := rfl
  have e3 : Layout.oSigTmp = 31648 := rfl
  have e4 : Layout.nodeSlots = 520 := rfl
  rcases hnp with e | e
  · have := h4 e
    rw [e4] at this
    exact ⟨Layout.oN, hr, e, by rw [e1]; omega_using [], by rw [e1, e3]; simp only [Cn]; omega_using [this], h1, h2, h3, h6, h7, h8, hn⟩
  · have := h5 e
    exact ⟨Layout.oRoots, hr, e, by rw [e2]; omega_using [], by rw [e2, e3]; simp only [Cn]; omega_using [this], h1, h2, h3, h6, h7, h8, hn⟩

/-! ## A call of `thash4` on the lanes `A` -/

section Call
variable {p : Params}

/-- `thashArgs` for the lanes `A`, messages of `len` bytes. -/
theorem args_ok (hn : p.n ≤ 32) {S : Addr} {len : Nat} (hlen : len < 2 ^ 31) {t : State} (hbx : t.gpr .rbx = S)
    {Q : State → Prop}
    (k : ∀ u, u.gpr .rdi = at' S Layout.oA → u.gpr .rsi = BitVec.ofNat 64 Layout.strideA →
      u.gpr .rdx = BitVec.ofNat 64 len → u.gpr .rcx = at' S (Layout.oA + (p.n + 32)) → u.gpr .r8 = S →
      (∀ g, g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → g ≠ .rcx → g ≠ .r8 → u.gpr g = t.gpr g) →
      u.mem = t.mem → u.rd = t.rd → u.wr = t.wr → Q u) :
    WP isa (.block (Impl.SlhDsa.X86_64.thashArgs ⟨p.n, p.len⟩ Layout.oA Layout.strideA len)) t Q := by
  simp only [Impl.SlhDsa.X86_64.thashArgs, Layout.msgOff]
  refine Proof.Sha3.X86_64.wp_mov fun u₁ v₁ => Proof.Sha3.X86_64.wp_addi fun u₂ v₂ =>
    Proof.Sha3.X86_64.wp_mov32i fun u₃ v₃ => Proof.Sha3.X86_64.wp_mov32i fun u₄ v₄ =>
    Proof.Sha3.X86_64.wp_mov fun u₅ v₅ => Proof.Sha3.X86_64.wp_addi fun u₆ v₆ =>
    Proof.Sha3.X86_64.wp_mov fun u₇ v₇ => WP.block_nil ?_
  have hA : (Layout.oA : Nat) < 2 ^ 31 := by simp only [Layout.oA]; omega_using []
  have h7 : u₇.gpr .rdi = at' S Layout.oA := by
    rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), v₂.gpr, v₁.gpr, hbx, sx_ofNat hA]
  refine k u₇ h7 ?_ ?_ ?_ ?_ (fun g h1 h2 h3 h4 h5 => ?_) ?_ ?_ ?_
  · rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr]
    rfl
  · rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [hlen]
  · rw [v₇.other _ (by decide), v₆.gpr, v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.gpr, v₁.gpr, hbx, sx_ofNat hA, sx_ofNat (by omega_using [hn]), add_add]
  · rw [v₇.gpr, v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), hbx]
  · rw [v₇.other _ h5, v₆.other _ h4, v₅.other _ h4, v₄.other _ h3, v₃.other _ h2, v₂.other _ h1, v₁.other _ h1]
  · rw [v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  · rw [v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd]
  · rw [v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr]

/-- `args_ok`, with MXCSR kept. -/
theorem args_mx_ok (hn : p.n ≤ 32) {S : Addr} {len : Nat} (hlen : len < 2 ^ 31) {t : State} (hbx : t.gpr .rbx = S)
    {Q : State → Prop}
    (k : ∀ u, u.gpr .rdi = at' S Layout.oA → u.gpr .rsi = BitVec.ofNat 64 Layout.strideA →
      u.gpr .rdx = BitVec.ofNat 64 len → u.gpr .rcx = at' S (Layout.oA + (p.n + 32)) → u.gpr .r8 = S →
      (∀ g, g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → g ≠ .rcx → g ≠ .r8 → u.gpr g = t.gpr g) →
      u.mem = t.mem → u.rd = t.rd → u.wr = t.wr → u.mxcsr = t.mxcsr → Q u) :
    WP isa (.block (Impl.SlhDsa.X86_64.thashArgs ⟨p.n, p.len⟩ Layout.oA Layout.strideA len)) t Q :=
  WP.mono_mx (by rfl) (args_ok hn hlen hbx (Q := fun u => u.mxcsr = t.mxcsr → Q u)
    fun u h1 h2 h3 h4 h5 hg hm hr hw hmx => k u h1 h2 h3 h4 h5 hg hm hr hw hmx) fun _ hq hmx => hq hmx

/-- The lanes `A` and `work`, as the call narrows the regions to them. -/
abbrev callW (S : Addr) : List Region := [⟨at' S Layout.oA, 4 * Layout.strideA⟩, ⟨S, workLen⟩]

theorem scr0 (S : Addr) : S = S + BitVec.ofNat 64 0 := (BitVec.add_zero S).symm

/-- `(S + o).toNat`, with no wrap. -/
theorem toNat_at {S : Addr} {o : Nat} (h : S.toNat + o < 2 ^ 64) : (at' S o).toNat = S.toNat + o := by
  rw [at', BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h]),
    Nat.mod_eq_of_lt (by omega_using [h])]

/-- A part of `scratch` below `2¹⁶` is in it. -/
theorem sub_scr (S : Addr) {o l : Nat} (h : o + l ≤ 2 ^ 16) : Region.Sub ⟨at' S o, l⟩ ⟨S, 2 ^ 16⟩ :=
  Offset.sub_base S h

/-- Parts of `scratch` that do not overlap. -/
theorem disj_scr (S : Addr) {o l o' l' : Nat} (h : o + l ≤ o' ∨ o' + l' ≤ o) (h₁ : o + l ≤ 2 ^ 16)
    (h₂ : o' + l' ≤ 2 ^ 16) : Region.Disjoint ⟨at' S o, l⟩ ⟨at' S o', l'⟩ :=
  Offset.disjoint S h (by omega_using [h₁]) (by omega_using [h₂])

/-- A byte of `scratch` on entry to a call is as it was before it. -/
theorem callEntry_byte' (u : State) {S : Addr} (hd : (below (u.gpr .rsp) 8).Disjoint ⟨S, 2 ^ 16⟩) {o : Nat}
    (ho : o < 2 ^ 16) : u.callEntry.mem (at' S o) = u.mem (at' S o) :=
  Proof.Sha3.X86_64.callEntry_byte u (R := ⟨S, 2 ^ 16⟩) hd (Nat.pow_le_pow_right (by decide) (by decide)) ho

/-- `bytesAt` of memories that agree on its bytes. -/
theorem bytesAt_congr {m m' : Mem} {a : Addr} {L : Nat} (h : ∀ i < L, m (a + BitVec.ofNat 64 i) = m' (a + BitVec.ofNat 64 i)) :
    bytesAt m a L = bytesAt m' a L := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- `thash4`'s precondition at the entry of the call after `thashArgs`, and its regions. -/
theorem t4_entry (T : Thash4Impl p.n) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {stack : Nat}
    (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63) {S : Addr} {t u : State}
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (t.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (hrc : RcTable t.mem S)
    (h1 : u.gpr .rdi = at' S Layout.oA) (h2 : u.gpr .rsi = BitVec.ofNat 64 Layout.strideA)
    (h3 : u.gpr .rdx = BitVec.ofNat 64 (3 * p.n + 32)) (h4 : u.gpr .rcx = at' S (Layout.oA + (p.n + 32)))
    (h5 : u.gpr .r8 = S) (hg : ∀ g, g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → g ≠ .rcx → g ≠ .r8 → u.gpr g = t.gpr g)
    (hm : u.mem = t.mem) (hwr : u.wr = t.wr) :
    (thash4Contract p.n T.stack).pre (u.callEntry.withRegions [] (callW S)) ∧
      Covers ([] ++ callW S) (u.rd ++ u.wr) ∧ Covers (callW S) u.wr := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hn8 : p.n % 8 = 0 := by omega_using [hn]
  have eA : Layout.oA = 3296 := rfl
  have eS : Layout.strideA = 128 := rfl
  have hsp : u.gpr .rsp = t.gpr .rsp := hg _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hne : ∀ r : Reg, r ≠ .rsp → u.callEntry.gpr r = u.gpr r := fun r h => State.callEntry_gpr _ h
  -- the stack the call uses, below `rsp`, is outside `scratch`
  have hstk8 : (below (u.gpr .rsp) 8).Disjoint ⟨S, 2 ^ 16⟩ := by
    rw [hsp]; exact hstk.sub_left (below_sub (by omega_using [hst]) (by omega_using [hs63]))
  have hcallee : (below (u.callEntry.gpr .rsp) T.stack).Disjoint ⟨S, 2 ^ 16⟩ := by
    rw [State.callEntry_rsp, hsp]
    exact hstk.sub_left (fun x hx => below_sub (sp := t.gpr .rsp) (a := T.stack + 8) (by omega_using [hst])
      (by omega_using [hs63]) x (below_callee _ _ x hx))
  have hret : (retR u.callEntry).Disjoint ⟨S, 2 ^ 16⟩ := by
    have : retR u.callEntry = below (u.gpr .rsp) 8 := by simp [retR, State.callEntry_rsp]
    rw [this]; exact hstk8
  have lanes_scr : Region.Sub ⟨at' S Layout.oA, 4 * Layout.strideA⟩ ⟨S, 2 ^ 16⟩ := sub_scr S (by rw [eA, eS]; omega_using [])
  have work_scr : Region.Sub ⟨S, workLen⟩ ⟨S, 2 ^ 16⟩ := Region.sub_prefix (by simp [workLen])
  have hcm : Frame [below (u.gpr .rsp) 8] u.mem u.callEntry.mem := by
    rw [State.callEntry_mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have hgpr : ∀ r, r ≠ .rsp → (u.callEntry.withRegions [] (callW S)).gpr r = u.gpr r := fun r h => by
    rw [State.withRegions_gpr, hne _ h]
  have h128 : (BitVec.ofNat 64 Layout.strideA).toNat = 128 := by rw [eS]; rfl
  have hlen : (BitVec.ofNat 64 (3 * p.n + 32)).toNat = 3 * p.n + 32 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hn32])
  have hpre : (thash4Contract p.n T.stack).pre (u.callEntry.withRegions [] (callW S)) := by
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [State.withRegions_wr, hgpr _ (by decide), hgpr _ (by decide), hgpr _ (by decide), h1, h2, h5, h128]
      simp only [callW, eS]
    · rw [hgpr _ (by decide), hgpr _ (by decide), hgpr _ (by decide), h1, h2, h5, h128, scr0 S, ← scr0 S]
      conv => rhs; rw [scr0 S]
      exact disj_scr S (Or.inr (by rw [eA]; simp [workLen])) (by rw [eA]; omega_using []) (by simp [workLen])
    · rw [hgpr _ (by decide), hgpr _ (by decide), h1, h2, h128]
      exact hret.sub_right (by rw [show 4 * 128 = 4 * Layout.strideA by rw [eS]]; exact lanes_scr)
    · rw [hgpr _ (by decide), h5]; exact hret.sub_right work_scr
    · simp only [State.withRegions_gpr]; rw [hne .rdi (by decide), hne .rsi (by decide), h1, h2, h128]
      exact hcallee.sub_right (by rw [show 4 * 128 = 4 * Layout.strideA by rw [eS]]; exact lanes_scr)
    · simp only [State.withRegions_gpr]; rw [hne .r8 (by decide), h5]; exact hcallee.sub_right work_scr
    · rw [hgpr _ (by decide), hgpr _ (by decide), h1, h2, h128, toNat_at (by rw [eA]; omega_using [hS])]
      rw [eA]; omega_using [hS]
    · rw [hgpr _ (by decide), h5]; simp only [workLen]; omega_using [hS]
    · rw [hgpr _ (by decide), h3, hlen]; omega_using []
    · rw [hgpr _ (by decide), h3, hlen]; omega_using [hn8]
    · rw [hgpr _ (by decide), hgpr _ (by decide), h3, h2, hlen, h128]; omega_using [hn32]
    · rw [hgpr _ (by decide), hgpr _ (by decide), h4, h1, add_add]
    · rw [hgpr _ (by decide), h2, h128]; omega_using [hn32]
    · rw [State.withRegions_mem, hgpr _ (by decide), h5]
      intro r hr k hk
      rw [← hrc r hr k hk, ← hm]
      refine hcm.readW (r := ⟨S + BitVec.ofNat 64 (1600 + 32 * r + 8 * k), 8⟩) (w := 64)
        (Region.contains_self (S + BitVec.ofNat 64 (1600 + 32 * r + 8 * k)) 8) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_singleton] at hr'; subst hr'
      exact (hstk8.sub_right (sub_scr S (by omega_using [hr, hk]))).symm
  have hw' : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr := by rw [hwr]; exact hw
  have hcov : Covers (callW S) u.wr := Covers.of_sub fun r hr => by
    simp only [callW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hw', Layout.oA, rfl, by show Layout.oA + 4 * Layout.strideA ≤ 2 ^ 16; rw [eA, eS]; omega_using []⟩
    · exact ⟨_, hw', 0, scr0 S, by simp [workLen]⟩
  exact ⟨hpre, by rw [List.nil_append]; exact Covers.right hcov, hcov⟩

/-- A call of `T` on the lanes `A`, messages of `3n + 32` bytes, from a state
whose `rbx` is `scratch` (`S`), with `stack` bytes below its stack pointer
for the call. Each lane's output is SHAKE256 of its message; only the
outputs, `work` (but its table) and the stack change. -/
theorem t4_ok (T : Thash4Impl p.n) (name : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {stack : Nat}
    (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63) {S : Addr} {t : State}
    (hbx : t.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (t.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (hrc : RcTable t.mem S) :
    WP isa (Impl.SlhDsa.X86_64.thashCall ⟨p.n, p.len⟩ name T.code Layout.oA Layout.strideA (3 * p.n + 32)) t
      (fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧ (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
        t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 ∧
        (∀ k < 4, bytesAt t'.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
          Spec.Sha3.shake256 (bytesAt t.mem (at' S (Layout.laneA k)) (3 * p.n + 32)) p.n) ∧
        Frame ((List.range 4).map (fun k => (⟨at' S (Layout.laneA k + p.n + 32), p.n⟩ : Region)) ++
          [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, below (t.gpr .rsp) stack]) t.mem t'.mem) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hn8 : p.n % 8 = 0 := by omega_using [hn]
  have eA : Layout.oA = 3296 := rfl
  have eS : Layout.strideA = 128 := rfl
  unfold Impl.SlhDsa.X86_64.thashCall
  refine WP.seq (args_mx_ok hn32 (len := 3 * p.n + 32) (by omega_using [hn32]) hbx
    fun u h1 h2 h3 h4 h5 hg hm hr hwr hmx₀ => ?_)
  have hsp : u.gpr .rsp = t.gpr .rsp := hg _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hne : ∀ r : Reg, r ≠ .rsp → u.callEntry.gpr r = u.gpr r := fun r h => State.callEntry_gpr _ h
  -- the stack the call uses, below `rsp`, is outside `scratch`
  have hstk8 : (below (u.gpr .rsp) 8).Disjoint ⟨S, 2 ^ 16⟩ := by
    rw [hsp]; exact hstk.sub_left (below_sub (by omega_using [hst]) (by omega_using [hs63]))
  have hcallee : (below (u.callEntry.gpr .rsp) T.stack).Disjoint ⟨S, 2 ^ 16⟩ := by
    rw [State.callEntry_rsp, hsp]
    exact hstk.sub_left (fun x hx => below_sub (sp := t.gpr .rsp) (a := T.stack + 8) (by omega_using [hst])
      (by omega_using [hs63]) x (below_callee _ _ x hx))
  have hret : (retR u.callEntry).Disjoint ⟨S, 2 ^ 16⟩ := by
    have : retR u.callEntry = below (u.gpr .rsp) 8 := by simp [retR, State.callEntry_rsp]
    rw [this]; exact hstk8
  have lanes_scr : Region.Sub ⟨at' S Layout.oA, 4 * Layout.strideA⟩ ⟨S, 2 ^ 16⟩ := sub_scr S (by rw [eA, eS]; omega_using [])
  have work_scr : Region.Sub ⟨S, workLen⟩ ⟨S, 2 ^ 16⟩ := Region.sub_prefix (by simp [workLen])
  have hcm : Frame [below (u.gpr .rsp) 8] u.mem u.callEntry.mem := by
    rw [State.callEntry_mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have hgpr : ∀ r, r ≠ .rsp → (u.callEntry.withRegions [] (callW S)).gpr r = u.gpr r := fun r h => by
    rw [State.withRegions_gpr, hne _ h]
  have h128 : (BitVec.ofNat 64 Layout.strideA).toNat = 128 := by rw [eS]; rfl
  have hlen : (BitVec.ofNat 64 (3 * p.n + 32)).toNat = 3 * p.n + 32 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hn32])
  obtain ⟨hpre, hcovl, hcov⟩ := t4_entry T hn hst hs63 hw hS hstk hrc h1 h2 h3 h4 h5 hg hm hwr
  have hd : 8 * T.code.depth + 16 < 2 ^ 64 := by have := T.depth_le; omega_using [this]
  refine WP.call_mx T.verified.1 T.nosp hd hpre hcovl hcov
    fun s' hrd hwr' hcs hf _ ⟨s₂, hm₂, _, hpost⟩ hmx => ?_
  have hentry : ∀ o, o < 2 ^ 16 → u.callEntry.mem (at' S o) = t.mem (at' S o) := fun o ho => by
    rw [← hm]
    exact callEntry_byte' u hstk8 ho
  have hlane : ∀ k < 4, Layout.laneA k = Layout.oA + 128 * k := fun k _ => by rw [Layout.laneA, eS]
  refine ⟨by rw [hrd, hr], by rw [hwr', hwr], fun r hr' => ?_, by rw [hmx, hmx₀], fun k hk => ?_, ?_⟩
  · have hne5 : r ≠ .rdi ∧ r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx ∧ r ≠ .r8 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hcs r hr', hg r hne5.1 hne5.2.1 hne5.2.2.1 hne5.2.2.2.1 hne5.2.2.2.2]
  · have e := hpost.1 k hk
    simp only [outAt, msg, State.withRegions_gpr, State.withRegions_mem, hne .rcx (by decide), hne .rsi (by decide),
      hne .rdi (by decide), hne .rdx (by decide), h1, h2, h3, h4, h128, hlen, hm₂] at e
    rw [add_add, show Layout.oA + (p.n + 32) + k * 128 = Layout.laneA k + p.n + 32 by
      rw [hlane k hk]; omega_using [], add_add, show Layout.oA + k * 128 = Layout.laneA k by
      rw [hlane k hk]; omega_using []] at e
    rw [e]
    congr 1
    refine bytesAt_congr fun i hi => ?_
    have hb : Layout.laneA k + i < 2 ^ 16 := by rw [hlane k hk, eA]; omega_using [hk, hi, hn32]
    rw [add_add]
    exact hentry (Layout.laneA k + i) hb
  · have f1 : Frame ((List.range 4).map (fun k => (⟨at' S (Layout.laneA k + p.n + 32), p.n⟩ : Region)) ++
        [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, below (t.gpr .rsp) stack]) u.mem u.callEntry.mem :=
      hcm.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨below (t.gpr .rsp) stack, by simp, by rw [hsp]; exact below_sub (by omega_using [hst]) (by omega_using [hs63])⟩
    have f2 := hpost.2
    simp only [thash4Changes, State.withRegions_gpr, State.withRegions_mem, hm₂] at f2
    refine (hm ▸ f1).trans (f2.sub fun r hr => ?_)
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with ⟨k, hk, rfl⟩ | rfl | rfl | rfl
    · refine ⟨⟨at' S (Layout.laneA k + p.n + 32), p.n⟩,
        List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩), ?_⟩
      rw [outAt, State.withRegions_gpr, hne .rcx (by decide), hne .rsi (by decide), h4, h2, h128, add_add, show Layout.oA + (p.n + 32) + k * 128 = Layout.laneA k + p.n + 32 by
        rw [hlane k hk]; omega_using []]
      exact fun _ h => h
    · exact ⟨⟨S, 1600⟩, by simp, by rw [hne .r8 (by decide), h5]; exact fun _ h => h⟩
    · exact ⟨⟨at' S 2368, 32⟩, by simp, by rw [hne .r8 (by decide), h5]; exact fun _ h => h⟩
    · refine ⟨below (t.gpr .rsp) stack, by simp, ?_⟩
      rw [State.callEntry_rsp, hsp]
      exact fun x hx => below_sub (sp := t.gpr .rsp) (a := T.stack + 8) (by omega_using [hst]) (by omega_using [hs63]) x
        (below_callee _ _ x hx)
end Call

end VG.Proof.SlhDsa.X86_64.Levels
