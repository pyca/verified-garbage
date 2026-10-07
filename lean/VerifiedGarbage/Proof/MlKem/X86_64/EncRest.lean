import VerifiedGarbage.Proof.MlKem.X86_64.EncBase
import VerifiedGarbage.Proof.MlKem.X86_64.Prfs
import VerifiedGarbage.Proof.MlKem.X86_64.FragEM

/-!
# ML-KEM on x86-64: K-PKE.Encrypt, the ciphertext

When every entry of `Â` was sampled: `y` (`y_ok`), `t̂` (`t_ok`), the
products `NTT⁻¹(Â^⊺ ∘ ŷ)` and `NTT⁻¹(t̂^⊺ ∘ ŷ)` (`mul_ok`), `u` to the
ciphertext (`u_ok`) and `v` to the ciphertext (`v_ok`). Between the steps,
`ER ny nt`: the first `ny` of `y` and `nt` of `t̂` are done; then `EU nu`:
the products, and the first `nu` of `u`. Each with its constant time, for a
given `ρ`.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Enc

open VG.Impl.MlKem.X86_64.Encrypt

variable {rbs wbs : List (Reg × Nat)} {E : Ptr} {L : Kem}

/-- The steps done after the matrix. -/
structure ER (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (ny nt : Nat) (s : State) : Prop where
  ok : allOk L.k (rhoE L ek) (L.k * L.k)
  i : EIn L C E ek m r s
  r15 : s.gpr .r15 = 1
  mat : ∀ e < L.k * L.k, PolyIs s.mem (pa s (pS (L.pA + e))) (aHat (rhoE L ek) (e / L.k) (e % L.k))
  prf : ∀ N < 2 * L.k + 1, bytesAt s.mem (pa s (prfO L N)) 128 = prf 2 r (BitVec.ofNat 8 N)
  y : ∀ k < ny, PolyIs s.mem (pa s (pS k)) (cbd r k)
  t : ∀ i < nt, PolyIs s.mem (pa s (pS (L.k + i))) (ekT ek i)

/-- A piece that writes `ws` keeps `ER ny nt`. -/
def erChk (L : Kem) (bs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (ny nt : Nat)
    (ws : List (Ptr × Nat)) : Bool :=
  inKeep L bs chk E ws && (List.range (L.k * L.k)).all (fun e => keepB bs ws (pS (L.pA + e)) 1024) &&
    (List.range (2 * L.k + 1)).all (fun N => keepB bs ws (prfO L N) 128) &&
    (List.range ny).all (fun k => keepB bs ws (pS k) 1024) &&
    (List.range nt).all (fun i => keepB bs ws (pS (L.k + i)) 1024)

theorem ER.keep {C : Ctx rbs wbs} {ek m r : List Byte} {ny nt : Nat} {s s' : State}
    (h : ER L C E ek m r ny nt s) {ws : List (Ptr × Nat)} (hP : PPost s s' ws)
    (hc : erChk L (rbs ++ wbs) C.chk E ny nt ws = true) : ER L C E ek m r ny nt s' := by
  simp only [erChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨hin, kA⟩, kR⟩, kY⟩, kT⟩ := hc
  have L₀ := C.lay h.i.out
  exact ⟨h.ok, h.i.keep hP.b hin, by rw [hP.cs .r15 (by decide)]; exact h.r15,
    fun e he => L₀.keepPoly hP.b (kA e he) (h.mat e he),
    fun N hN => by rw [L₀.keepBytes hP.b (kR N hN)]; exact h.prf N hN, fun k hk => L₀.keepPoly hP.b (kY k hk) (h.y k hk),
    fun i hi => L₀.keepPoly hP.b (kT i hi) (h.t i hi)⟩

/-- `Â[i, j]`, from the entries. -/
theorem ER.matIJ {C : Ctx rbs wbs} {ek m r : List Byte} {ny nt : Nat} {s : State}
    (h : ER L C E ek m r ny nt s) {i j : Nat} (hi : i < L.k) (hj : j < L.k) :
    PolyIs s.mem (pa s (L.aS i j)) (aHat (rhoE L ek) i j) := by
  have := h.mat (L.k * i + j) (ij_lt hi hj)
  rwa [(divmod_ij hj).1, (divmod_ij hj).2, ← aS_ij] at this

theorem EB.flag {C : Ctx rbs wbs} {ek m r : List Byte} {s s' : State} (h : EB L C E ek m r (L.k * L.k) s)
    (hP : PPost s s' []) (hc : inKeep L (rbs ++ wbs) C.chk E [] = true)
    (hk : ∀ e < L.k * L.k, keepB (rbs ++ wbs) [] (pS (L.pA + e)) 1024 = true)
    (hsb : keepB (rbs ++ wbs) [] (sc oSB) 32 = true) : EB L C E ek m r (L.k * L.k) s' := by
  have L₀ := C.lay h.i.out
  exact ⟨h.i.keep hP.b hc, by rw [L₀.keepBytes hP.b hsb]; exact h.sb, by rw [hP.cs .r15 (by decide)]; exact h.m.r15,
    fun e he f hf => L₀.keepPoly hP.b (hk e he) (h.m.mat e he f hf)⟩

/-- After the matrix, when every `SampleNTT` succeeded. -/
structure ER0 (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (s : State) : Prop where
  ok : allOk L.k (rhoE L ek) (L.k * L.k)
  i : EIn L C E ek m r s
  r15 : s.gpr .r15 = 1
  mat : ∀ e < L.k * L.k, PolyIs s.mem (pa s (pS (L.pA + e))) (aHat (rhoE L ek) (e / L.k) (e % L.k))

theorem ER0.start {C : Ctx rbs wbs} {ek m r : List Byte} {s : State} (h : EB L C E ek m r (L.k * L.k) s)
    (ho : allOk L.k (rhoE L ek) (L.k * L.k)) : ER0 L C E ek m r s :=
  ⟨ho, h.i, by rw [h.m.r15, ifp ho], fun e he => h.m.mat e he _ (aHat_eq ho (div_lt_k he) (mod_lt_k he))⟩

/-- The steps, for the `ρ` of `ek`. -/
abbrev ERρ (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (ny nt : Nat) (s : State) : Prop :=
  ∃ ek m r, rhoE L ek = ρ ∧ ER L C E ek m r ny nt s

/-! ## The outputs of `PRF₂` -/

def prfsEChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Bool :=
  prfsChk bs wbs (2 * L.k + 1) L.oPR L.lPW && inKeep L bs chk E (prfsW (2 * L.k + 1) L.oPR L.lPW) &&
    (List.range (L.k * L.k)).all (fun e => keepB bs (prfsW (2 * L.k + 1) L.oPR L.lPW) (pS (L.pA + e)) 1024)

theorem prfsE_ok (v : Sample4Impl) {C : Ctx rbs wbs} (hk : L.k ≤ 4) (hc : prfsEChk L (rbs ++ wbs) wbs C.chk E = true)
    {ek m r : List Byte} {s : State} (h : ER0 L C E ek m r s) :
    WP isa (v.callee.prfs 0 (2 * L.k + 1) L.oPR L.lPW) s fun s' =>
      PPost s s' (prfsW (2 * L.k + 1) L.oPR L.lPW) ∧ ER L C E ek m r 0 0 s' := by
  simp only [prfsEChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨hpc, hin⟩, kA⟩ := hc
  have L₀ := C.lay h.i.out
  refine WP.mono (v.prfs_ok L₀ C.bs (by omega) hpc) fun s' ⟨hP, hb⟩ => ⟨hP, h.ok, h.i.keep hP.b hin,
    by rw [hP.cs .r15 (by decide)]; exact h.r15, fun e he => L₀.keepPoly hP.b (kA e he) (h.mat e he), fun N hN => ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rw [prfO, hP.pa rbx_cs, hb N hN, h.i.r, Nat.zero_add]

/-- After the matrix, for the `ρ` of `ek`. -/
abbrev ER0ρ (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (s : State) : Prop :=
  ∃ ek m r, rhoE L ek = ρ ∧ ER0 L C E ek m r s

theorem prfsE_tr (v : Sample4Impl) {C : Ctx rbs wbs} (hk : L.k ≤ 4) (hc : prfsEChk L (rbs ++ wbs) wbs C.chk E = true)
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ER0ρ L C E ρ x ∧ ER0ρ L C E ρ y) (v.callee.prfs 0 (2 * L.k + 1) L.oPR L.lPW)
      (fun x y => LRel rbs wbs x y ∧ ERρ L C E ρ 0 0 x ∧ ERρ L C E ρ 0 0 y) := by
  have hc' := hc
  simp only [prfsEChk, Bool.and_eq_true] at hc'
  exact RelCT.stepL C.bs (RelCT.mono (v.prfs_tr C.bs (by omega) hc'.1.1) (fun _ _ h => h.1) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (prfsE_ok v hk hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩

/-! ## `y` -/

def yChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (N : Nat) : Bool :=
  twoChk bs wbs (prfO L N) 128 (pS N) 1024 && erChk L bs chk E N 0 [(pS N, 1024)]

theorem y_ok {A : Arith} (hA : ArithOk A) {C : Ctx rbs wbs} {N : Nat} (hN : N < L.k)
    (hc : yChk L (rbs ++ wbs) wbs C.chk E N = true) {ek m r : List Byte} {s : State} (h : ER L C E ek m r N 0 s) :
    WP isa (y L A N) s fun s' => PPost s s' [(pS N, 1024)] ∧ ER L C E ek m r (N + 1) 0 s' := by
  simp only [yChk, Bool.and_eq_true] at hc
  have L₀ := C.lay h.i.out
  refine WP.mono (cbd2At_okL hA L₀ rbx_na hc.1) fun s' ⟨hP, hp⟩ => ?_
  have hk := h.keep hP hc.2
  refine ⟨hP, hk.ok, hk.i, hk.r15, hk.mat, hk.prf, fun k hk' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rcases (by omega : k < N ∨ k = N) with hk' | rfl
  · exact hk.y k hk'
  · rw [h.prf k (by omega), ← hP.pa rbx_cs] at hp; exact hp

theorem y_tr {A : Arith} (hA : ArithOk A) {C : Ctx rbs wbs} {N : Nat} (hN : N < L.k)
    (hc : yChk L (rbs ++ wbs) wbs C.chk E N = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ERρ L C E ρ N 0 x ∧ ERρ L C E ρ N 0 y) (y L A N)
      (fun x y => LRel rbs wbs x y ∧ ERρ L C E ρ (N + 1) 0 x ∧ ERρ L C E ρ (N + 1) 0 y) := by
  have hc' := hc
  simp only [yChk, Bool.and_eq_true] at hc'
  exact RelCT.stepL C.bs (RelCT.mono (cbd2At_trL hA rbx_na hc'.1) (fun _ _ h => h.1) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (y_ok hA hN hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩

/-! ## `t̂` -/

def tChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (i : Nat) : Bool :=
  twoChk bs wbs (E.1, E.2 + 384 * i) 384 (pS (L.k + i)) 1024 && erChk L bs chk E L.k i [(pS (L.k + i), 1024)]

theorem t_ok {A : Arith} (hA : ArithOk A) {C : Ctx rbs wbs} {i : Nat} (hi : i < L.k) (hc : tChk L (rbs ++ wbs) wbs C.chk E i = true)
    {ek m r : List Byte} {s : State} (h : ER L C E ek m r L.k i s) :
    WP isa (t L A E i) s fun s' => PPost s s' [(pS (L.k + i), 1024)] ∧ ER L C E ek m r L.k (i + 1) s' := by
  simp only [tChk, Bool.and_eq_true] at hc
  have L₀ := C.lay h.i.out
  refine WP.mono (dec12At_okL hA L₀ rbx_na hc.1) fun s' ⟨hP, hp⟩ => ?_
  have hk := h.keep hP hc.2
  refine ⟨hP, hk.ok, hk.i, hk.r15, hk.mat, hk.prf, hk.y, fun i' hi' => ?_⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact hk.t i' hi'
  · rw [hP.pa rbx_cs]
    have e : bytesAt s.mem (pa s (E.1, E.2 + 384 * i')) 384 = (ek.drop (384 * i')).take 384 := by
      rw [← h.i.ek]
      show _ = ((bytesAt s.mem (pa s E) (384 * L.k + 32)).drop (384 * i')).take 384
      rw [bytesAt_slice _ _ (show 384 * i' + 384 ≤ 384 * L.k + 32 by omega), pa, pa, off_add]
    rw [e] at hp
    exact hp

theorem t_tr {A : Arith} (hA : ArithOk A) {C : Ctx rbs wbs} {i : Nat} (hi : i < L.k) (hc : tChk L (rbs ++ wbs) wbs C.chk E i = true)
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ERρ L C E ρ L.k i x ∧ ERρ L C E ρ L.k i y) (t L A E i)
      (fun x y => LRel rbs wbs x y ∧ ERρ L C E ρ L.k (i + 1) x ∧ ERρ L C E ρ L.k (i + 1) y) := by
  have hc' := hc
  simp only [tChk, Bool.and_eq_true] at hc'
  exact RelCT.stepL C.bs (RelCT.mono (dec12At_trL hA rbx_na hc'.1) (fun _ _ h => h.1) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (t_ok hA hi hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩

/-! ## The products -/

/-- `NTT⁻¹(Â^⊺ ∘ ŷ)[i]` for `i < k`, and `NTT⁻¹(t̂^⊺ ∘ ŷ)` for `i = k`. -/
def encW (L : Kem) (ek r : List Byte) (i : Nat) : Poly :=
  if i < L.k then nttInv (KPke.dotK (fun j => aHat (rhoE L ek) j i) (encY r) L.k)
  else nttInv (KPke.dotK (ekT ek) (encY r) L.k)

/-- After the products: the first `nu` of `u` are in the ciphertext, the
others of the products are in place. -/
structure EU (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (nu : Nat) (s : State) : Prop
    extends ER L C E ek m r L.k L.k s where
  w : ∀ i < L.k + 1, nu ≤ i → PolyIs s.mem (pa s (pS (L.pU + i))) (encW L ek r i)
  u : ∀ i < nu, bytesAt s.mem (pa s (sc (L.oCT + 32 * L.du * i))) (32 * L.du) =
    compressEncode L.du (KPke.encU L.p (aHat (rhoE L ek)) r i)

/-- A piece that writes `ws` keeps `ER k k`, the products from `nw` and the first `nu` of `u`. -/
def euChk (L : Kem) (bs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (nw nu : Nat)
    (ws : List (Ptr × Nat)) : Bool :=
  erChk L bs chk E L.k L.k ws &&
    (List.range (L.k + 1)).all (fun i => !decide (nw ≤ i) || keepB bs ws (pS (L.pU + i)) 1024) &&
    (List.range nu).all (fun i => keepB bs ws (sc (L.oCT + 32 * L.du * i)) (32 * L.du))

theorem EU.keep {C : Ctx rbs wbs} {ek m r : List Byte} {nu nw : Nat} {s s' : State} (h : EU L C E ek m r nu s)
    (hn : nu ≤ nw) {ws : List (Ptr × Nat)} (hP : PPost s s' ws) (hc : euChk L (rbs ++ wbs) C.chk E nw nu ws = true) :
    ER L C E ek m r L.k L.k s' ∧ (∀ i < L.k + 1, nw ≤ i → PolyIs s'.mem (pa s' (pS (L.pU + i))) (encW L ek r i)) ∧
      ∀ i < nu, bytesAt s'.mem (pa s' (sc (L.oCT + 32 * L.du * i))) (32 * L.du) =
        compressEncode L.du (KPke.encU L.p (aHat (rhoE L ek)) r i) := by
  simp only [euChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hc
  obtain ⟨⟨hr, kw⟩, ku⟩ := hc
  have L₀ := C.lay h.i.out
  exact ⟨h.toER.keep hP hr, fun i hi hi' => L₀.keepPoly hP.b ((kw i hi).resolve_left fun h' => h' hi')
    (h.w i hi (Nat.le_trans hn hi')), fun i hi => by rw [L₀.keepBytes hP.b (ku i hi)]; exact h.u i hi⟩

theorem ER.vred {C : Ctx rbs wbs} {ek m r : List Byte} {s : State} (h : ER L C E ek m r L.k L.k s) :
    VecReduced s.mem (pa s (pS L.pA)) (L.k * L.k) ∧ VecReduced s.mem (pa s (pS L.k)) L.k ∧
      VecReduced s.mem (pa s (pS 0)) L.k :=
  ⟨vecReduced_pS fun e he => (h.mat e he).1, vecReduced_pS fun i hi => (h.t i hi).1,
    vecReduced_pS fun j hj => by rw [Nat.zero_add]; exact (h.y j hj).1⟩

/-- The outputs of `vg_mlkem*_encrypt_mul`, for the inputs of `ER k k`. -/
theorem ER.prods {C : Ctx rbs wbs} {ek m r : List Byte} {s : State} (h : ER L C E ek m r L.k L.k s) {i : Nat}
    (hi : i < L.k + 1) :
    ((((mulMatTVec L.k (matAt s.mem (pa s (pS L.pA)) L.k) ((vecAt s.mem (pa s (pS 0)) L.k).map ntt)).map nttInv) ++
      [nttInv (dot (vecAt s.mem (pa s (pS L.k)) L.k) ((vecAt s.mem (pa s (pS 0)) L.k).map ntt))]).getD i zero) =
      encW L ek r i := by
  have hy : (vecAt s.mem (pa s (pS 0)) L.k).map ntt = (List.range L.k).map (encY r) := by
    rw [vecAt_pS, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    rw [Function.comp_apply, Nat.zero_add, (h.y j (List.mem_range.mp hj)).2]
    rfl
  rw [hy]
  by_cases h' : i < L.k
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [EncMul.mulMatTVec_length]; exact h'),
      ← List.getD_eq_getElem?_getD, EncMul.mulMatTVec_getD _ _ _ _ h', encW, ifp h']
    refine congrArg nttInv ?_
    have hcol : EncMul.colE s.mem (pa s (pS L.pA)) L.k i = (List.range L.k).map fun j => aHat (rhoE L ek) j i := by
      simp only [EncMul.colE, matAt, List.map_map]
      refine List.map_congr_left fun j hj => ?_
      have hj := List.mem_range.mp hj
      rw [Function.comp_apply, List.getD_eq_getElem?_getD, vecAt, List.getElem?_map, List.getElem?_range h',
        Option.map_some, Option.getD_some, BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add, ← pa_pS,
        show L.pA + (L.k * j + i) = L.pA + L.k * j + i by omega]
      exact (h.matIJ hj h').2
    rw [hcol, KPke.dot_eq_dotK]
  · have hik : i = L.k := by omega
    subst hik
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [EncMul.mulMatTVec_length]),
      EncMul.mulMatTVec_length, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, encW,
      ifn (Nat.lt_irrefl _)]
    refine congrArg nttInv ?_
    have ht : vecAt s.mem (pa s (pS L.k)) L.k = (List.range L.k).map (ekT ek) := by
      rw [vecAt_pS]
      exact List.map_congr_left fun j hj => (h.t j (List.mem_range.mp hj)).2
    rw [ht, KPke.dot_eq_dotK]

/-- The products: `vg_mlkem*_encrypt_mul`. -/
def emEChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Bool :=
  emChk bs wbs L.k (pS L.pU) (pS L.pA) (pS L.k) (pS 0) (pS L.pZ) &&
    erChk L bs chk E L.k L.k [(pS L.pU, 1024 * (L.k + 1)), (pS L.pZ, 4096)]

theorem mul_ok {A : Arith} (hA : ArithOk A) (hk : L.k = 3 ∨ L.k = 4) {C : Ctx rbs wbs}
    (hc : emEChk L (rbs ++ wbs) wbs C.chk E = true) {ek m r : List Byte} {s : State} (h : ER L C E ek m r L.k L.k s) :
    WP isa (mul L A) s fun s' => PPost s s' [(pS L.pU, 1024 * (L.k + 1)), (pS L.pZ, 4096)] ∧
      EU L C E ek m r 0 s' := by
  simp only [emEChk, Bool.and_eq_true] at hc
  have L₀ := C.lay h.i.out
  have hr := h.vred
  refine WP.mono (encMulAt_okL hA hk L₀ rbx_na rbx_na rbx_na rbx_na hc.1 hr.1 hr.2.1 hr.2.2) fun s' ⟨hP, hv⟩ => ?_
  refine ⟨hP, h.keep hP hc.2, fun i hi _ => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have e := hv.2 i hi
  rw [← pa_pS, ← hP.pa rbx_cs, h.prods hi] at e
  exact e

/-- `EU nu`, for the `ρ` of `ek`. -/
abbrev EUρ (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (nu : Nat) (s : State) : Prop :=
  ∃ ek m r, rhoE L ek = ρ ∧ EU L C E ek m r nu s

theorem mul_tr {A : Arith} (hA : ArithOk A) (hk : L.k = 3 ∨ L.k = 4) {C : Ctx rbs wbs}
    (hc : emEChk L (rbs ++ wbs) wbs C.chk E = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ERρ L C E ρ L.k L.k x ∧ ERρ L C E ρ L.k L.k y) (mul L A)
      (fun x y => LRel rbs wbs x y ∧ EUρ L C E ρ 0 x ∧ EUρ L C E ρ 0 y) := by
  have hc' := hc
  simp only [emEChk, Bool.and_eq_true] at hc'
  exact RelCT.stepL C.bs (RelCT.mono (encMulAt_trL hA hk rbx_na rbx_na rbx_na rbx_na hc'.1)
    (fun x y ⟨hl, ⟨_, _, _, _, h₁⟩, ⟨_, _, _, _, h₂⟩⟩ => ⟨hl, h₁.vred, h₂.vred⟩) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (mul_ok hA hk hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩

/-! ## `u` -/

abbrev uW (L : Kem) (i : Nat) : List (Ptr × Nat) :=
  [(pS 15, 1024)] ++ [(pS (L.pU + i), 1024)] ++ [(sc (L.oCT + 32 * L.du * i), 32 * L.du)]

def uChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (i : Nat) : Bool :=
  twoChk bs wbs (prfO L (L.k + i)) 128 (pS 15) 1024 && keepB bs [(pS 15, 1024)] (pS (L.pU + i)) 1024 &&
    accChk bs wbs (pS (L.pU + i)) (pS 15) &&
    twoChk bs wbs (pS (L.pU + i)) 1024 (sc (L.oCT + 32 * L.du * i)) (32 * L.du) &&
    euChk L bs chk E (i + 1) i (uW L i)

theorem u_ok {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : KemCalls L wc wd) {C : Ctx rbs wbs}
    {i : Nat} (hi : i < L.k) (hc : uChk L (rbs ++ wbs) wbs C.chk E i = true) {ek m r : List Byte} {s : State}
    (h : EU L C E ek m r i s) :
    WP isa (u L A i) s fun s' => PPost s s' (uW L i) ∧ EU L C E ek m r (i + 1) s' := by
  simp only [uChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hpc, hkw⟩, hac⟩, htw⟩, hrc⟩ := hc
  have L₀ := C.lay h.i.out
  unfold u
  refine WP.seq (WP.mono (cbd2At_okL hA L₀ rbx_na hpc) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have L₁ := L₀.post hP₁.b C.bs
  rw [h.prf (L.k + i) (by omega), ← hP₁.pa rbx_cs] at hp₁
  have hw₁ := L₀.keepPoly hP₁.b hkw (h.w i (by omega) (Nat.le_refl _))
  refine WP.seq (WP.mono (addAt_ok hA L₁ rbx_na hac hw₁.1 hp₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_)
  have L₂ := L₁.post hP₂.b C.bs
  rw [hw₁.2, hp₁.2, ← hP₂.pa rbx_cs] at hp₂
  refine WP.mono (ceCall_okL K.ce L₂ rbx_na htw K.du.1 hp₂.1) fun s₃ ⟨hP₃, hb₃⟩ => ?_
  have hP := PPost.app (PPost.app hP₁ hP₂ (by simp [calleeSaved])) hP₃ (by simp [calleeSaved])
  obtain ⟨hk, hw, hu⟩ := h.keep (Nat.le_succ i) hP hrc
  refine ⟨hP, hk, hw, fun i' hi' => ?_⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact hu i' hi'
  · rw [hP₃.pa rbx_cs, hb₃, hp₂.2, encW, ifp hi]; rfl

theorem u_tr {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : KemCalls L wc wd) {C : Ctx rbs wbs}
    {i : Nat} (hi : i < L.k) (hc : uChk L (rbs ++ wbs) wbs C.chk E i = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ EUρ L C E ρ i x ∧ EUρ L C E ρ i y) (u L A i)
      (fun x y => LRel rbs wbs x y ∧ EUρ L C E ρ (i + 1) x ∧ EUρ L C E ρ (i + 1) y) := by
  have hc' := hc
  simp only [uChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨hpc, hkw⟩, hac⟩, htw⟩, _⟩ := hc'
  refine RelCT.stepL C.bs ?_ fun x ⟨ek, m, r, eρ, hx⟩ =>
    WP.mono (u_ok hA K hi hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩
  unfold u
  refine RelCT.mono (RelCT.seqL (I := fun x => Reduced x.mem (pa x (pS (L.pU + i))))
    (J := fun x => Reduced x.mem (pa x (pS (L.pU + i))) ∧ Reduced x.mem (pa x (pS 15))) C.bs
      (RelCT.mono (cbd2At_trL hA rbx_na hpc) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x Lx hx => WP.mono (cbd2At_okL hA Lx rbx_na hpc) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, Lx.keepRed hP.b hkw hx, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS (L.pU + i)))) C.bs (addAt_tr hA rbx_na hac)
      (fun x Lx hx => WP.mono (addAt_ok hA Lx rbx_na hac hx.1 hx.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
      (ceCall_trL K.ce rbx_na htw K.du.1)))
    (fun x y ⟨hl, ⟨_, _, _, _, h₁⟩, ⟨_, _, _, _, h₂⟩⟩ =>
      ⟨hl, (h₁.w i (by omega) (Nat.le_refl _)).1, (h₂.w i (by omega) (Nat.le_refl _)).1⟩) fun _ _ h => h

/-! ## `v` -/

abbrev vW (L : Kem) : List (Ptr × Nat) := [(pS 15, 1024)] ++ [(pS (L.pU + L.k), 1024)] ++ [(pS 15, 1024)] ++
  [(pS (L.pU + L.k), 1024)] ++ [(sc (L.oCT + 32 * L.du * L.k), 32 * L.dv)]

def vChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Bool :=
  twoChk bs wbs (prfO L (2 * L.k)) 128 (pS 15) 1024 && keepB bs [(pS 15, 1024)] (pS (L.pU + L.k)) 1024 &&
    accChk bs wbs (pS (L.pU + L.k)) (pS 15) && twoChk bs wbs (sc oM) 32 (pS 15) 1024 &&
    inKeep L bs chk E ([(pS 15, 1024)] ++ [(pS (L.pU + L.k), 1024)]) &&
    twoChk bs wbs (pS (L.pU + L.k)) 1024 (sc (L.oCT + 32 * L.du * L.k)) (32 * L.dv) &&
    euChk L bs chk E (L.k + 1) L.k (vW L)

theorem v_ok {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : KemCalls L wc wd) {C : Ctx rbs wbs}
    (hc : vChk L (rbs ++ wbs) wbs C.chk E = true) {ek m r : List Byte} {s : State} (h : EU L C E ek m r L.k s) :
    WP isa (v L A) s fun s' => PPost s s' (vW L) ∧ C.Out s' ∧ s'.gpr .r15 = 1 ∧
      bytesAt s'.mem (pa s' (sc L.oCT)) L.ctLen = KPke.ct L.p (aHat (rhoE L ek)) ek m r := by
  simp only [vChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨hpc, hkw⟩, hac⟩, hdd⟩, hi₂⟩, htw⟩, hrc⟩ := hc
  have L₀ := C.lay h.i.out
  unfold v
  refine WP.seq (WP.mono (cbd2At_okL hA L₀ rbx_na hpc) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have L₁ := L₀.post hP₁.b C.bs
  rw [h.prf (2 * L.k) (by omega), ← hP₁.pa rbx_cs] at hp₁
  have hw₁ := L₀.keepPoly hP₁.b hkw (h.w L.k (by omega) (Nat.le_refl _))
  refine WP.seq (WP.mono (addAt_ok hA L₁ rbx_na hac hw₁.1 hp₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_)
  have hP₁₂ := PPost.app hP₁ hP₂ (by simp [calleeSaved])
  have e₂ := h.i.keep hP₁₂.b hi₂
  have L₂ := C.lay e₂.out
  rw [hw₁.2, hp₁.2, ← hP₂.pa rbx_cs] at hp₂
  refine WP.seq (WP.mono (ddCall_okL ddImpl L₂ (d := 1) rbx_na hdd (by decide)) fun s₃ ⟨hP₃, hp₃⟩ => ?_)
  have L₃ := L₂.post hP₃.b C.bs
  rw [e₂.m, ← hP₃.pa rbx_cs] at hp₃
  have hq₃ := L₂.keepPoly hP₃.b hkw hp₂
  refine WP.seq (WP.mono (addAt_ok hA L₃ rbx_na hac hq₃.1 hp₃.1) fun s₄ ⟨hP₄, hp₄⟩ => ?_)
  have L₄ := L₃.post hP₄.b C.bs
  rw [hq₃.2, hp₃.2, ← hP₄.pa rbx_cs] at hp₄
  refine WP.mono (ceCall_okL K.ce L₄ (d := L.dv) rbx_na htw K.dv.1 hp₄.1) fun s₅ ⟨hP₅, hb₅⟩ => ?_
  have hP₄' := PPost.app (PPost.app hP₁₂ hP₃ (by simp [calleeSaved])) hP₄ (by simp [calleeSaved])
  have hP := PPost.app hP₄' hP₅ (by simp [calleeSaved])
  obtain ⟨hk, -, hu⟩ := h.keep (Nat.le_succ _) hP hrc
  rw [hP₄'.pa rbx_cs] at hb₅
  refine ⟨hP, hk.i.out, hk.r15, ?_⟩
  rw [Kem.ctLen, Params.ctLen, show 32 * (L.p.du * L.p.k + L.p.dv) = 32 * L.du * L.k + 32 * L.dv by
      simp only [Kem.du, Kem.dv, Kem.k]; rw [Nat.mul_add, Nat.mul_assoc], hP.pa rbx_cs, sc, bytesAt_split,
    hb₅, hp₄.2, encW, ifn (Nat.lt_irrefl _), KPke.ct]
  refine congrArg (· ++ _) (bytesAt_catK _ _ _ _ _ _ L.k fun i hi => ?_)
  rw [← hP.pa (p := sc (L.oCT + 32 * L.du * i)) rbx_cs]
  exact hu i hi

/-! ## The end of K-PKE.Encrypt -/

/-- The end: `r15` as `allOk`, and the ciphertext if it is 1. -/
structure EOut (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (s : State) : Prop where
  out : C.Out s
  r15 : s.gpr .r15 = if allOk L.k (rhoE L ek) (L.k * L.k) then 1 else 0
  ct : allOk L.k (rhoE L ek) (L.k * L.k) →
    bytesAt s.mem (pa s (sc L.oCT)) L.ctLen = KPke.ct L.p (aHat (rhoE L ek)) ek m r

/-- The end, for the `ρ` of `ek`. -/
abbrev EOρ (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (s : State) : Prop :=
  ∃ ek m r, rhoE L ek = ρ ∧ EOut L C E ek m r s

theorem v_tr {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : KemCalls L wc wd) {C : Ctx rbs wbs}
    (hc : vChk L (rbs ++ wbs) wbs C.chk E = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ EUρ L C E ρ L.k x ∧ EUρ L C E ρ L.k y) (v L A)
      (fun x y => LRel rbs wbs x y ∧ EOρ L C E ρ x ∧ EOρ L C E ρ y) := by
  have hc' := hc
  simp only [vChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨hpc, hkw⟩, hac⟩, hdd⟩, _⟩, htw⟩, _⟩ := hc'
  refine RelCT.stepL C.bs ?_ fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (v_ok hA K hc hx) fun _ ⟨hP, ho, h15, hct⟩ =>
    ⟨⟨_, hP.b⟩, ek, m, r, eρ, ho, by rw [h15, ifp hx.ok], fun _ => hct⟩
  unfold v
  refine RelCT.mono (RelCT.seqL (I := fun x => Reduced x.mem (pa x (pS (L.pU + L.k))))
    (J := fun x => Reduced x.mem (pa x (pS (L.pU + L.k))) ∧ Reduced x.mem (pa x (pS 15))) C.bs
      (RelCT.mono (cbd2At_trL hA rbx_na hpc) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x Lx hx => WP.mono (cbd2At_okL hA Lx rbx_na hpc) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, Lx.keepRed hP.b hkw hx, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS (L.pU + L.k)))) C.bs (addAt_tr hA rbx_na hac)
      (fun x Lx hx => WP.mono (addAt_ok hA Lx rbx_na hac hx.1 hx.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS (L.pU + L.k))) ∧ Reduced x.mem (pa x (pS 15))) C.bs
      (RelCT.mono (ddCall_trL ddImpl (d := 1) rbx_na hdd (by decide)) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x Lx hx => WP.mono (ddCall_okL ddImpl Lx (d := 1) rbx_na hdd (by decide)) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, Lx.keepRed hP.b hkw hx, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS (L.pU + L.k)))) C.bs (addAt_tr hA rbx_na hac)
      (fun x Lx hx => WP.mono (addAt_ok hA Lx rbx_na hac hx.1 hx.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
      (ceCall_trL K.ce (d := L.dv) rbx_na htw K.dv.1)))))
    (fun x y ⟨hl, ⟨_, _, _, _, h₁⟩, ⟨_, _, _, _, h₂⟩⟩ =>
      ⟨hl, (h₁.w L.k (by omega) (Nat.le_refl _)).1, (h₂.w L.k (by omega) (Nat.le_refl _)).1⟩) fun _ _ h => h

end Enc

end VG.Proof.MlKem.X86_64
