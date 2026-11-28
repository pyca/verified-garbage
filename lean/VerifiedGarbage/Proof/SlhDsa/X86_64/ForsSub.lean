module

-- separate module: the subtrees, which `ForsTop` does not rebuild when it changes

public import VerifiedGarbage.Proof.SlhDsa.X86_64.ForsTree
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.SlhDsa.Lemmas

/-!
# SLH-DSA (SHAKE) on x86-64: `forsSign`, the subtrees of a tree

`subtreeBody`, a subtree: its leaves, its heights, the next subtree
(`sub_ok`); and the loop of the `2^(a-s)` subtrees of tree `t`
(`subs_ok`): the private key value of the tree's index and its
authentication path's nodes below height `s` in the signature, the subtree
roots at `oRoots`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Fors

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Impl.SlhDsa.X86_64.Fors
open VG.Proof.SlhDsa (fld)

theorem zf_eq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have : BitVec.ofNat 64 a - BitVec.ofNat 64 b ≠ 0 := fun e => h (by
      have e' := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
        show (0 : BitVec 64).toNat = 0 from rfl] at e'
      omega_using [e', ha, hb])
    rw [decide_eq_false h]; simpa using this

/-- A leaf, as the code computes it, is the specification's. -/
theorem leafv_node {p : Params} {pkSeed a16 skSeed : List Byte} (h16 : a16.length = 16) {kp : Nat} (hkp : kp < 2 ^ 32)
    (x : Nat) : leafv p pkSeed a16 skSeed kp x = node p skSeed pkSeed a16 kp x 0 := by
  rw [node, forsNode_zero, node_adrs h16, forsSkGen, sk_adrs h16 kp hkp]
  rfl

/-- What the subtrees change. -/
abbrev subW (p : Params) (S AU sp : Addr) (stack : Nat) : List Region :=
  [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S (Layout.oVar 2 2), 16⟩, ⟨at' S (Layout.oFrame 4), 128⟩,
    ⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩, ⟨at' S Layout.oRoots, 1024⟩, ⟨AU, (p.a + 1) * p.n⟩, below sp stack] ++
  (List.range 4).map fun k => (⟨at' S (Layout.laneA k + p.n + 16), 16 + 2 * p.n⟩ : Region)

/-- The state before subtree `u` of tree `tt`, from the entry state `t₀` of
the loop (signature zeroed). -/
structure ST (p : Params) (stack : Nat) (S AU : Addr) (pkSeed a16 skSeed : List Byte) (kp tt idx : Nat)
    (t₀ : State) (u : Nat) (t : State) : Prop where
  fix : Fix t₀ t
  env : Env p t.mem S pkSeed a16
  sk : SkAt p t.mem S skSeed
  v1 : t.mem.readW (at' S (Layout.oVar 2 1)) 64 = AU
  v2 : t.mem.readW (at' S (Layout.oVar 2 2)) 64 = BitVec.ofNat 64 (u * 2 ^ s p.a)
  v4 : t.mem.readW (at' S (Layout.oVar 2 4)) 64 = BitVec.ofNat 64 (tt * 2 ^ p.a)
  skp : ∀ j < p.n, t.mem (AU + BitVec.ofNat 64 j) =
    if idx < u * 2 ^ s p.a then skv p pkSeed a16 skSeed kp (tt * 2 ^ p.a + idx) j else 0
  auth : ∀ r < s p.a, bytesAt t.mem (AU + BitVec.ofNat 64 p.n + BitVec.ofNat 64 (r * p.n)) p.n =
    acc p skSeed pkSeed a16 kp tt idx (s p.a) p.a r u
  high : ∀ r, s p.a ≤ r → r < p.a → bytesAt t.mem (AU + BitVec.ofNat 64 p.n + BitVec.ofNat 64 (r * p.n)) p.n =
    toByte 0 p.n
  roots : ∀ u' < u, bytesAt t.mem (at' S (Layout.oRoots + u' * p.n)) p.n =
    node p skSeed pkSeed a16 kp (tt * 2 ^ (p.a - s p.a) + u') (s p.a)
  frame : Frame (subW p S AU (t₀.gpr .rsp) stack) t₀.mem t.mem

/-- A part of the tree's signature `⟨AU, (a + 1)·n⟩` in `⟨SG, L⟩`. -/
theorem sigSub {SG AU : Addr} {L dA o l : Nat} (hAU : AU = SG + BitVec.ofNat 64 dA) (h : dA + o + l ≤ L) :
    Region.Sub ⟨AU + BitVec.ofNat 64 o, l⟩ ⟨SG, L⟩ := by
  rw [hAU, Levels.add_add]; exact Offset.sub_base SG (by omega_using [h])

theorem sigIn {SG AU : Addr} {L dA o l : Nat} {wr : List Region} (hw : (⟨SG, L⟩ : Region) ∈ wr)
    (hAU : AU = SG + BitVec.ofNat 64 dA) (h : dA + o + l ≤ L) (hf : SG.toNat + L ≤ 2 ^ 64) (hl : 0 < l) :
    InRegions wr (AU + BitVec.ofNat 64 o) l :=
  ⟨_, hw, by rw [hAU, Levels.add_add]; exact Offset.contains_base SG (by omega_using [h]) (by omega_using [h, hf, hl])⟩

/-- Two parts of the tree's signature that do not overlap. -/
theorem sigD (AU : Addr) {o l o' l' : Nat} (h : o + l ≤ o' ∨ o' + l' ≤ o) (h₁ : o + l ≤ 2 ^ 64) (h₂ : o' + l' ≤ 2 ^ 64) :
    Region.Disjoint ⟨AU + BitVec.ofNat 64 o, l⟩ ⟨AU + BitVec.ofNat 64 o', l'⟩ := Offset.disjoint AU h h₁ h₂

/-- The block before the leaves: variable 3 zeroed. -/
theorem zero3_ok {S : Addr} {u : State} (hbx : u.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (var 3) .rax]) u fun u' =>
      (∀ g, g ≠ .rax → u'.gpr g = u.gpr g) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.mxcsr = u.mxcsr ∧
      u'.mem.readW (at' S (Layout.oVar 2 3)) 64 = BitVec.ofNat 64 0 ∧
      Frame [⟨at' S (Layout.oVar 2 3), 8⟩] u.mem u'.mem := by
  refine WP.mono_mx (by rfl) (Q := fun u' => u'.mxcsr = u.mxcsr → _) ?_ fun _ h hm => h hm
  refine Proof.Sha3.X86_64.wp_mov32i fun u₁ e₁ => Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 2 3))
    (by rw [var, Proof.Sha3.X86_64.ea_at, e₁.other _ (by decide), hbx])
    (by rw [e₁.wr]; exact Levels.in_scr hw (by rw [oVar2]; omega_using [])) fun u₂ g₂ m₂ r₂ w₂ => WP.block_nil fun hm => ?_
  refine ⟨fun g h => by rw [g₂, e₁.other _ h], by rw [r₂, e₁.rd], by rw [w₂, e₁.wr], hm, ?_, ?_⟩
  · rw [m₂, Mem.readW_writeW_self64, e₁.gpr]; rfl
  · rw [m₂, e₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-- The block after the heights: the next subtree, compared with `2^a`. -/
theorem next2_ok {S : Addr} {U2 D A : Nat} {u : State} (hbx : u.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr)
    (h2 : u.mem.readW (at' S (Layout.oVar 2 2)) 64 = BitVec.ofNat 64 U2) (hD : D < 2 ^ 31) (hA : A < 2 ^ 31)
    (hU : U2 + D < 2 ^ 63) :
    WP isa (.block [.mov .rax (.mem (var 2)), .alu .add .rax (.imm (BitVec.ofNat 32 D)), .store (var 2) .rax,
        .alu .cmp .rax (.imm (BitVec.ofNat 32 A))]) u fun u' =>
      (∀ g, g ≠ .rax → u'.gpr g = u.gpr g) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.mxcsr = u.mxcsr ∧
      u'.mem.readW (at' S (Layout.oVar 2 2)) 64 = BitVec.ofNat 64 (U2 + D) ∧
      u'.zf = some (decide (U2 + D = A)) ∧ Frame [⟨at' S (Layout.oVar 2 2), 8⟩] u.mem u'.mem := by
  refine WP.mono_mx (by rfl) (Q := fun u' => u'.mxcsr = u.mxcsr → _) ?_ fun _ h hm => h hm
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 2 2)) (by rw [var, Proof.Sha3.X86_64.ea_at, hbx])
    (Levels.in_scr' hw (by rw [oVar2]; omega_using [])) fun u₁ e₁ => Proof.Sha3.X86_64.wp_addi fun u₂ e₂ => ?_
  refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 2 2))
    (by rw [var, Proof.Sha3.X86_64.ea_at, e₂.other _ (by decide), e₁.other _ (by decide), hbx])
    (by rw [e₂.wr, e₁.wr]; exact Levels.in_scr hw (by rw [oVar2]; omega_using [])) fun u₃ g₃ m₃ r₃ w₃ => ?_
  refine Levels.wp_cmpi fun u₄ g₄ m₄ r₄ w₄ z₄ => WP.block_nil fun hm => ?_
  have hax : u₂.gpr .rax = BitVec.ofNat 64 (U2 + D) := by
    rw [e₂.gpr, e₁.gpr, h2, Levels.sx_ofNat hD, BitVec.ofNat_add_ofNat]
  refine ⟨fun g h => by rw [g₄, g₃, e₂.other _ h, e₁.other _ h], by rw [r₄, r₃, e₂.rd, e₁.rd],
    by rw [w₄, w₃, e₂.wr, e₁.wr], hm, ?_, ?_, ?_⟩
  · rw [m₄, m₃, Mem.readW_writeW_self64, hax]
  · rw [z₄, g₃, hax, Levels.sx_ofNat hA, zf_eq (by omega_using [hU]) (by omega_using [hA])]
  · rw [m₄, m₃, e₂.mem, e₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-- What the tree's loops need of their entry state `t₀`. -/
structure SC (p : Params) (stack : Nat) (S SG AU : Addr) (L dA tt idx : Nat) (t₀ : State) : Prop where
  hf : p.family = .shake
  hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32
  a6 : 6 ≤ p.a
  a14 : p.a ≤ 14
  bx : t₀.gpr .rbx = S
  kp : (t₀.gpr .r12).toNat < 2 ^ 32
  r13 : t₀.gpr .r13 = BitVec.ofNat 64 idx
  idx : idx < 2 ^ p.a
  w : (⟨S, 2 ^ 16⟩ : Region) ∈ t₀.wr
  wG : (⟨SG, L⟩ : Region) ∈ t₀.wr
  AU : AU = SG + BitVec.ofNat 64 dA
  dA : dA + (p.a + 1) * p.n ≤ L
  Gf : SG.toNat + L ≤ 2 ^ 64
  fit : S.toNat + 2 ^ 16 ≤ 2 ^ 64
  stk : (below (t₀.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩
  Gd : Region.Disjoint ⟨SG, L⟩ ⟨S, Layout.oSigTmp⟩
  Gs : Region.Disjoint ⟨SG, L⟩ (below (t₀.gpr .rsp) stack)
  tt : (tt + 1) * 2 ^ p.a < 2 ^ 32

theorem xor_zero8 (x : Byte) : x ^^^ (0 : Byte) = x := BitVec.xor_zero

theorem mul_pow_div (u : Nat) {s r : Nat} (h : r ≤ s) : u * 2 ^ s / 2 ^ r = u * 2 ^ (s - r) := by
  rw [show 2 ^ s = 2 ^ (s - r) * 2 ^ r by rw [← Nat.pow_add, Nat.sub_add_cancel h], ← Nat.mul_assoc,
    Nat.mul_div_cancel _ (Nat.two_pow_pos r)]

theorem s_le (a : Nat) : s a ≤ a := Nat.min_le_left _ _

theorem s_ge {a : Nat} (h : 6 ≤ a) : 6 ≤ s a := Nat.le_min.mpr ⟨h, by decide⟩

theorem a_s {a : Nat} (h : a ≤ 14) : a - s a ≤ 5 := by unfold s; omega_using [h]

/-- A subtree. -/
theorem sub_ok {p : Params} (T : Thash4Impl p.n) (name ln : String) {stack : Nat} (hst : T.stack + 24 ≤ stack)
    (hs63 : stack < 2 ^ 63) {S SG AU : Addr} {L dA tt idx : Nat} {pkSeed a16 skSeed : List Byte} {t₀ : State}
    (C : SC p stack S SG AU L dA tt idx t₀) {u : Nat} {t : State} (hu : u < 2 ^ (p.a - s p.a))
    (hI : ST p stack S AU pkSeed a16 skSeed (t₀.gpr .r12).toNat tt idx t₀ u t) :
    WP isa (subtreeBody ⟨p.n, p.len⟩ p.a name ln T.code) t fun t' =>
      t'.zf = some (decide ((u + 1) * 2 ^ s p.a = 2 ^ p.a)) ∧
      ST p stack S AU pkSeed a16 skSeed (t₀.gpr .r12).toNat tt idx t₀ (u + 1) t' := by
  have hn := C.hn
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hs6 := s_ge C.a6
  have hsa := s_le p.a
  have has := a_s C.a14
  have hs9 : s p.a ≤ 9 := Nat.min_le_right _ _
  have h2s : 2 ^ s p.a ≤ 512 := by
    calc 2 ^ s p.a ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hs9
      _ = 512 := rfl
  have h2a : 2 ^ p.a ≤ 2 ^ 14 := Nat.pow_le_pow_right (by decide) C.a14
  have hU : 2 ^ (p.a - s p.a) ≤ 32 := by
    calc 2 ^ (p.a - s p.a) ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) has
      _ = 32 := rfl
  have hUs : 2 ^ (p.a - s p.a) * 2 ^ s p.a = 2 ^ p.a := by rw [← Nat.pow_add, Nat.sub_add_cancel hsa]
  have hu1 : (u + 1) * 2 ^ s p.a ≤ 2 ^ p.a := by rw [← hUs]; exact Nat.mul_le_mul_right _ hu
  have hsp : t.gpr .rsp = t₀.gpr .rsp := hI.fix.cs _ (by simp [calleeSaved])
  have hbx : t.gpr .rbx = S := by rw [hI.fix.cs _ (by simp [calleeSaved]), C.bx]
  have hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr := by rw [hI.fix.wr]; exact C.w
  have h16 : a16.length = 16 := by rw [← hI.env.adrsA 0 (by decide)]; simp [bytesAt]
  have hd4 : 4 ∣ 2 ^ s p.a := by simpa using (Nat.pow_dvd_pow 2 (show 2 ≤ s p.a by omega_using [hs6]))
  have hdAn : dA + (p.a + 1) * p.n ≤ L := C.dA
  have hu1' : u * 2 ^ s p.a + 2 ^ s p.a ≤ 2 ^ p.a := by rw [← Nat.succ_mul]; exact hu1
  have h64 : 64 ≤ 2 ^ s p.a := by
    calc 64 = 2 ^ 6 := rfl
      _ ≤ 2 ^ s p.a := Nat.pow_le_pow_right (by decide) hs6
  have han : (p.a + 1) * p.n = p.n + p.a * p.n := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  have hsn : s p.a * p.n ≤ p.a * p.n := Nat.mul_le_mul_right _ hsa
  have hc520 : (2 ^ s p.a + 8) * p.n ≤ 16640 := by
    have := Nat.mul_le_mul (show 2 ^ s p.a + 8 ≤ 520 by omega_using [h2s]) hn32; omega_using [this]
  have hAN : (p.a + 1) * p.n ≤ 15 * 32 := Nat.mul_le_mul (by omega_using [C.a14]) hn32
  -- the tree's signature, against the regions the parts change
  have dXs : ∀ {o l : Nat}, o + l ≤ (p.a + 1) * p.n → ∀ {R : Region}, Region.Sub R ⟨S, Layout.oSigTmp⟩ →
      Region.Disjoint ⟨AU + BitVec.ofNat 64 o, l⟩ R := fun {o l} h {R} hR =>
    (C.Gd.sub_left (sigSub C.AU (by omega_using [h, hdAn]))).sub_right hR
  have dXk : ∀ {o l : Nat}, o + l ≤ (p.a + 1) * p.n →
      Region.Disjoint ⟨AU + BitVec.ofNat 64 o, l⟩ (below (t₀.gpr .rsp) stack) := fun {o l} h =>
    C.Gs.sub_left (sigSub C.AU (by omega_using [h, hdAn]))
  have sS : ∀ {o l : Nat}, o + l ≤ 31648 → Region.Sub ⟨at' S o, l⟩ ⟨S, Layout.oSigTmp⟩ := fun h =>
    Offset.sub_base S (by rw [show Layout.oSigTmp = 31648 from rfl]; exact h)
  unfold subtreeBody
  refine WP.seq (WP.mono (zero3_ok hbx hw) fun t₁ ⟨g₁, r₁, w₁, mx₁, v3₁, f₁⟩ => ?_)
  have k₁ : ∀ q, q < 31648 → (q < 2728 ∨ 2736 ≤ q) → t₁.mem (at' S q) = t.mem (at' S q) := fun q hq h =>
    keepS f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dS S (by rw [oVar2]; omega_using [h]) (by omega_using [hq]) (by rw [oVar2]; omega_using [])
  have kw : ∀ (m m' : Mem) (rs : List Region), Frame rs m m' → ∀ i, i < 9 →
      (∀ r ∈ rs, Region.Disjoint ⟨at' S (Layout.oVar 2 i), 8⟩ r) →
      m'.readW (at' S (Layout.oVar 2 i)) 64 = m.readW (at' S (Layout.oVar 2 i)) 64 := fun m m' rs f i _ h => keepSW f h
  have dv3 : ∀ i, i < 9 → i ≠ 3 → ∀ r ∈ [(⟨at' S (Layout.oVar 2 3), 8⟩ : Region)],
      Region.Disjoint ⟨at' S (Layout.oVar 2 i), 8⟩ r := fun i hi h3 r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact dS S (by rw [oVar2, oVar2]; omega_using [h3]) (by rw [oVar2]; omega_using [hi]) (by rw [oVar2]; omega_using [])
  have hbx₁ : t₁.gpr .rbx = S := by rw [g₁ _ (by decide), hbx]
  have hsp₁ : t₁.gpr .rsp = t₀.gpr .rsp := by rw [g₁ _ (by decide), hsp]
  have hw₁ : (⟨S, 2 ^ 16⟩ : Region) ∈ t₁.wr := by rw [w₁]; exact hw
  have hfix₁ : Fix t₀ t₁ := hI.fix.trans ⟨fun r hr => g₁ r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), r₁, w₁, by rw [mx₁]⟩
  have hL0 : LS p stack S AU pkSeed a16 skSeed (t₀.gpr .r12).toNat (tt * 2 ^ p.a) (u * 2 ^ s p.a) idx t₁ 0 t₁ :=
    ⟨Fix.refl _, env_bytes hn32 hI.env fun q hq => k₁ q (by simp only [EnvB] at hq; omega_using [hq])
        (by simp only [EnvB] at hq; omega_using [hq]),
      sk_bytes hI.sk fun q h₁ h₂ => k₁ q (by omega_using [h₂, hn32]) (.inr (by omega_using [h₁])),
      by rw [kw _ _ _ f₁ 1 (by decide) (dv3 1 (by decide) (by decide)), hI.v1],
      by rw [kw _ _ _ f₁ 2 (by decide) (dv3 2 (by decide) (by decide)), hI.v2], v3₁,
      by rw [kw _ _ _ f₁ 4 (by decide) (dv3 4 (by decide) (by decide)), hI.v4],
      fun _ h => absurd h (by omega_using []), fun j _ => by rw [ite_eq_right (by omega_using [])], Frame.refl _ _⟩
  -- the leaves
  have hsig : ∀ w < p.n / 8, InRegions t₁.wr (AU + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' => by
    rw [w₁, hI.fix.wr]; exact sigIn C.wG C.AU (by omega_using [hw', hdAn, han, hn]) C.Gf (by decide)
  have hm4 : 0 + 4 * (2 ^ s p.a / 4) = 2 ^ s p.a := by rw [Nat.zero_add]; exact Nat.mul_div_cancel' hd4
  refine WP.seq (WP.mono (leaves_ok T name hn C.hf (by omega_using [hst]) hs63 (KP := t₀.gpr .r12) hbx₁
    (by rw [hfix₁.cs _ (by simp [calleeSaved])]) C.kp (by rw [hfix₁.cs _ (by simp [calleeSaved]), C.r13])
    (by omega_using [C.idx, h2a]) hw₁ C.fit (by rw [hsp₁]; exact C.stk)
    (by have := C.tt; rw [Nat.succ_mul] at this; omega_using [this, hu1']) hsig
    (by rw [show AU = AU + BitVec.ofNat 64 0 from (BitVec.add_zero AU).symm]; exact dXs (by omega_using [han]) (fun _ h => h))
    (by rw [hsp₁, show AU = AU + BitVec.ofNat 64 0 from (BitVec.add_zero AU).symm]; exact dXk (by omega_using [han]))
    (m := 2 ^ s p.a / 4) (by omega_using [hm4, h64]) hm4 hL0) fun t₂ L₂ => ?_)
  have hfix₂ : Fix t₀ t₂ := hfix₁.trans L₂.fix
  have hr12₂ : t₂.gpr .r12 = t₀.gpr .r12 := hfix₂.cs _ (by simp [calleeSaved])
  have hbx₂ : t₂.gpr .rbx = S := by rw [hfix₂.cs _ (by simp [calleeSaved]), C.bx]
  have hsp₂ : t₂.gpr .rsp = t₀.gpr .rsp := hfix₂.cs _ (by simp [calleeSaved])
  have hX : tt * 2 ^ p.a + u * 2 ^ s p.a < 2 ^ 32 := by
    have := C.tt; rw [Nat.succ_mul] at this; omega_using [this, hu1']
  have hdv4 : 2 ^ s p.a ∣ tt * 2 ^ p.a := Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 hsa) _
  have hR : u * 2 ^ s p.a / 2 ^ s p.a = u := Nat.mul_div_cancel _ (Nat.two_pow_pos _)
  refine WP.seq (WP.mono (subHeights_ok T name ln hn C.hf hst hs63 (L := L) (dA := dA) (U2 := u * 2 ^ s p.a)
    (V4 := tt * 2 ^ p.a) (idx := idx) (pkSeed := pkSeed) (a16 := a16) (skSeed := skSeed) hbx₂
    (by rw [hr12₂]; exact C.kp) (by rw [hfix₂.cs _ (by simp [calleeSaved]), C.r13]) (by omega_using [C.idx, h2a])
    (by rw [hfix₂.wr]; exact C.w) (by rw [hfix₂.wr]; exact C.wG) C.AU (by omega_using [hdAn, han, hsn]) C.Gf C.fit
    (by rw [hsp₂]; exact C.stk) C.Gd (by rw [hsp₂]; exact C.Gs) L₂.env L₂.v1 L₂.v2 L₂.v4 hX hdv4
    (Nat.dvd_mul_left _ _) (by rw [hR]; omega_using [hu, hU]) hs6 fun i hi => by
      rw [hr12₂, L₂.nodes i hi, leafv_node h16 C.kp]) fun t₃ H => ?_)
  have hfix₃ : Fix t₀ t₃ := hfix₂.trans H.fix
  have hbx₃ : t₃.gpr .rbx = S := by rw [hfix₃.cs _ (by simp [calleeSaved]), C.bx]
  have hcnt : Layout.oN + (2 ^ s p.a + 8) * p.n ≤ 31648 := by
    have := Nat.mul_le_mul (show 2 ^ s p.a + 8 ≤ 520 by omega_using [h2s]) hn32
    rw [show Layout.oN = 12640 from rfl]; omega_using [this]
  have hslot : Layout.oRoots + u * 2 ^ s p.a / 2 ^ s p.a * p.n + p.n ≤ 30304 := by
    rw [hR, show Layout.oRoots = 29280 from rfl]
    have := Nat.mul_le_mul (show u + 1 ≤ 32 by omega_using [hu, hU]) hn32
    rw [Nat.succ_mul] at this; omega_using [this]
  -- the bytes of `scratch` the heights leave
  have kH : ∀ q, q < 31648 → 1600 ≤ q → (q < 2368 ∨ 2400 ≤ q) → (q < 2912 ∨ 3040 ≤ q) →
      (∀ k < 4, q < Layout.laneA k + p.n + 16 ∨ Layout.laneA k + p.n + 16 + (16 + 2 * p.n) ≤ q) →
      (q < Layout.oN ∨ Layout.oN + (2 ^ s p.a + 8) * p.n ≤ q) →
      (q < Layout.oRoots + u * 2 ^ s p.a / 2 ^ s p.a * p.n ∨ Layout.oRoots + u * 2 ^ s p.a / 2 ^ s p.a * p.n + p.n ≤ q) →
      t₃.mem (at' S q) = t₂.mem (at' S q) := fun q hq h₀ h₁ h₂ h₃ h₄ h₅ => keepS H.frame fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [levelsChanges, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with ⟨k, hk, rfl⟩ | rfl | rfl | rfl | rfl
      · exact dS S (h₃ k hk |>.imp (by omega_using []) id) (by omega_using [hq])
          (by rw [laneA_eq]; omega_using [hk, hn32])
      · exact Offset.disjoint_base S h₀ (by omega_using [hq])
      · exact dS S (by omega_using [h₁]) (by omega_using [hq]) (by decide)
      · exact dS S (by rw [show Layout.oFrame 4 = 2912 from rfl]; omega_using [h₂]) (by omega_using [hq]) (by decide)
      · exact dS S (by omega_using [h₄]) (by omega_using [hq]) (by omega_using [hcnt])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (dXs (o := p.n) (l := s p.a * p.n) (by omega_using [han, hsn]) (sS (by omega_using [hq]))).symm
      · rw [hsp₂]; exact (C.stk.sub_right (Levels.sub_scr S (by omega_using [hq]))).symm
      · exact dS S (by omega_using [h₅]) (by omega_using [hq]) (by omega_using [hslot])
  -- the next subtree
  have hv2₃ : t₃.mem.readW (at' S (Layout.oVar 2 2)) 64 = BitVec.ofNat 64 (u * 2 ^ s p.a) := by
    rw [← L₂.v2]
    exact Mem.readW_congr fun j hj => by
      rw [Levels.add_add, oVar2]
      exact kH _ (by omega_using [hj]) (by omega_using []) (.inr (by omega_using [])) (.inl (by omega_using [hj]))
        (fun k hk => .inl (by rw [laneA_eq]; omega_using [hj])) (.inl (by rw [show Layout.oN = 12640 from rfl]; omega_using [hj]))
        (.inl (by rw [show Layout.oRoots = 29280 from rfl]; omega_using [hj]))
  have h2s31 : 2 ^ s p.a < 2 ^ 31 := by omega_using [h2s]
  have h2a31 : 2 ^ p.a < 2 ^ 31 := by
    have : (2 : Nat) ^ 14 = 16384 := rfl; omega_using [h2a, this]
  refine WP.mono (next2_ok hbx₃ (by rw [hfix₃.wr]; exact C.w) hv2₃ h2s31 h2a31 (by omega_using [hu1', h2a31]))
    fun t₄ ⟨g₄, r₄, w₄, mx₄, v2₄, z₄, f₄⟩ => ?_
  have k₄ : ∀ q, q < 31648 → (q < 2720 ∨ 2728 ≤ q) → t₄.mem (at' S q) = t₃.mem (at' S q) := fun q hq h =>
    keepS f₄ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dS S (by rw [oVar2]; omega_using [h]) (by omega_using [hq]) (by rw [oVar2]; omega_using [])
  -- `scratch` from `t₂` to `t₄`
  have k24 : ∀ q, q < 31648 → 1600 ≤ q → (q < 2368 ∨ 2400 ≤ q) → (q < 2720 ∨ 2728 ≤ q) → (q < 2912 ∨ 3040 ≤ q) →
      (∀ k < 4, q < Layout.laneA k + p.n + 16 ∨ Layout.laneA k + p.n + 16 + (16 + 2 * p.n) ≤ q) →
      (q < Layout.oN ∨ Layout.oN + (2 ^ s p.a + 8) * p.n ≤ q) →
      (q < Layout.oRoots + u * 2 ^ s p.a / 2 ^ s p.a * p.n ∨ Layout.oRoots + u * 2 ^ s p.a / 2 ^ s p.a * p.n + p.n ≤ q) →
      t₄.mem (at' S q) = t₂.mem (at' S q) := fun q hq h₀ h₁ h₁' h₂ h₃ h₄ h₅ => by
    rw [k₄ q hq h₁', kH q hq h₀ h₁ h₂ h₃ h₄ h₅]
  have kw24 : ∀ i, i < 9 → i ≠ 2 → t₄.mem.readW (at' S (Layout.oVar 2 i)) 64 = t₂.mem.readW (at' S (Layout.oVar 2 i)) 64 :=
    fun i hi h2 => Mem.readW_congr fun j hj => by
      rw [Levels.add_add, oVar2]
      exact k24 _ (by omega_using [hi, hj]) (by omega_using []) (.inr (by omega_using [])) (by omega_using [h2, hj, hi])
        (.inl (by omega_using [hi, hj])) (fun k hk => .inl (by rw [laneA_eq]; omega_using [hi, hj]))
        (.inl (by rw [show Layout.oN = 12640 from rfl]; omega_using [hi, hj]))
        (.inl (by rw [show Layout.oRoots = 29280 from rfl]; omega_using [hi, hj]))
  -- the signature from `t` to `t₄`
  have bk : ∀ {rs : List Region} {m m' : Mem} (x : Addr), Frame rs m m' → (∀ r ∈ rs, Region.Disjoint ⟨x, 1⟩ r) →
      m' x = m x := fun x f h => by simpa using f.bytes (R := ⟨x, 1⟩) h (show 1 ≤ 2 ^ 64 by decide) (show 0 < 1 by decide)
  have dSub : ∀ o l, o + l ≤ (p.a + 1) * p.n → (o + l ≤ p.n ∨ p.n + s p.a * p.n ≤ o) →
      ∀ r ∈ levelsChanges p S (at' S Layout.oN) (2 ^ s p.a) ++ [⟨AU + BitVec.ofNat 64 p.n, s p.a * p.n⟩,
        below (t₂.gpr .rsp) stack, ⟨at' S (Layout.oRoots + u * 2 ^ s p.a / 2 ^ s p.a * p.n), p.n⟩],
        Region.Disjoint ⟨AU + BitVec.ofNat 64 o, l⟩ r := fun o l h₀ h r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact dXs h₀ (Levels.levelsChanges_low hn32 S (by rw [show Layout.oSigTmp = 31648 from rfl]; omega_using [hcnt]) r hr)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sigD AU h (by omega_using [h₀, hAN]) (by omega_using [han, hsn, h₀, hAN])
      · rw [hsp₂]; exact dXk h₀
      · exact dXs h₀ (sS (by omega_using [hslot]))
  have dLoop : ∀ o l, o + l ≤ (p.a + 1) * p.n → p.n ≤ o →
      ∀ r ∈ loopW p.n S AU (t₁.gpr .rsp) stack, Region.Disjoint ⟨AU + BitVec.ofNat 64 o, l⟩ r := fun o l h₀ h r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, laneRs, List.mem_map, List.mem_range] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨k, hk, rfl⟩
    · exact dXs h₀ (Region.sub_prefix (by rw [show Layout.oSigTmp = 31648 from rfl]; omega_using []))
    · exact dXs h₀ (sS (by omega_using []))
    · exact dXs h₀ (sS (by rw [oVar2]; omega_using []))
    · exact dXs h₀ (sS (by rw [show Layout.oN = 12640 from rfl, show Layout.nodeSlots = 520 from rfl]; omega_using []))
    · rw [show AU = AU + BitVec.ofNat 64 0 from (BitVec.add_zero AU).symm, Levels.add_add, Nat.zero_add]
      exact sigD AU (.inr (by omega_using [h])) (by omega_using [h₀, hAN]) (by omega_using [hn32])
    · rw [hsp₁]; exact dXk h₀
    · exact dXs h₀ (sS (by rw [laneA_eq]; omega_using [hk, hn32]))
  have dF : ∀ o l, o + l ≤ (p.a + 1) * p.n → ∀ r ∈ [(⟨at' S (Layout.oVar 2 3), 8⟩ : Region)],
      Region.Disjoint ⟨AU + BitVec.ofNat 64 o, l⟩ r := fun o l h₀ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dXs h₀ (sS (by rw [oVar2]; omega_using []))
  have dN : ∀ o l, o + l ≤ (p.a + 1) * p.n → ∀ r ∈ [(⟨at' S (Layout.oVar 2 2), 8⟩ : Region)],
      Region.Disjoint ⟨AU + BitVec.ofNat 64 o, l⟩ r := fun o l h₀ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dXs h₀ (sS (by rw [oVar2]; omega_using []))
  have hAUd : Region.Disjoint ⟨AU, p.n⟩ ⟨S, Layout.oSigTmp⟩ := by
    have := dXs (o := 0) (l := p.n) (by omega_using [han]) (fun _ h => h)
    rwa [BitVec.add_zero] at this
  have hr2 : ∀ r ≤ s p.a, u * 2 ^ s p.a / 2 ^ r = u * 2 ^ (s p.a - r) := fun r h => mul_pow_div u h
  have hr4 : ∀ r ≤ p.a, tt * 2 ^ p.a / 2 ^ r = tt * 2 ^ (p.a - r) := fun r h => mul_pow_div tt h
  refine ⟨by rw [z₄, Nat.succ_mul], ?_⟩
  refine ⟨hfix₃.trans ⟨fun r hr => g₄ r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), r₄, w₄, by rw [mx₄]⟩, ?env, ?sk,
    by rw [kw24 1 (by decide) (by decide), L₂.v1], by rw [v2₄, ← Nat.succ_mul],
    by rw [kw24 4 (by decide) (by decide), L₂.v4], fun j hj => ?_, fun r hr => ?_, fun r h₁ h₂ => ?_,
    fun u' hu' => ?_, ?_⟩
  case env =>
    refine env_bytes hn32 H.env fun q hq => ?_
    simp only [EnvB] at hq
    exact k₄ q (by omega_using [hq]) (by omega_using [hq])
  case sk =>
    refine sk_bytes L₂.sk fun q h₁ h₂ => k24 q (by omega_using [h₂, hn32]) (by omega_using [h₁]) (.inr (by omega_using [h₁]))
      (.inr (by omega_using [h₁])) (.inr (by omega_using [h₁, h₂, hn32])) (fun k hk => .inl (by rw [laneA_eq]; omega_using [h₂, hn32]))
      (.inl (by rw [show Layout.oN = 12640 from rfl]; omega_using [h₂, hn32]))
      (.inl (by rw [show Layout.oRoots = 29280 from rfl]; omega_using [h₂, hn32]))
  · -- the private key value
    rw [bk _ f₄ (dN j 1 (by omega_using [hj, han])), bk _ H.frame (dSub j 1 (by omega_using [hj, han]) (.inl (by omega_using [hj]))),
      L₂.skb j hj, bk _ f₁ (dF j 1 (by omega_using [hj, han])), hI.skp j hj]
    rw [Nat.succ_mul]
    by_cases e₁ : u * 2 ^ s p.a ≤ idx ∧ idx < u * 2 ^ s p.a + 2 ^ s p.a
    · rw [ite_eq_left e₁, ite_eq_right (by omega_using [e₁]), ite_eq_left (by omega_using [e₁]), xor_zero8]
    · rw [ite_eq_right e₁]
      by_cases e₂ : idx < u * 2 ^ s p.a
      · rw [ite_eq_left e₂, ite_eq_left (by omega_using [e₂])]
      · rw [ite_eq_right e₂, ite_eq_right (by omega_using [e₁, e₂])]
  · -- the path below height `s`
    have hrn : p.n + r * p.n + p.n ≤ (p.a + 1) * p.n := by
      have := Nat.mul_le_mul_right p.n (show r + 1 ≤ p.a by omega_using [hr, hsa]); rw [Nat.succ_mul] at this
      omega_using [this, han]
    rw [Levels.add_add, bytesAt_frame f₄ (dN _ _ hrn) (by omega_using [hn32]), ← Levels.add_add, H.auth r hr,
      Levels.add_add, bytesAt_frame L₂.frame (dLoop _ _ hrn (by omega_using [])) (by omega_using [hn32]),
      bytesAt_frame f₁ (dF _ _ hrn) (by omega_using [hn32]), ← Levels.add_add, hI.auth r hr, hr2 r (by omega_using [hr]),
      hr4 r (by omega_using [hr, hsa]), hr12₂]
    exact acc_succ p skSeed pkSeed a16 _ hn32 tt idx (s p.a) p.a r u
  · -- the path above it, still zero
    have hrn : p.n + r * p.n + p.n ≤ (p.a + 1) * p.n := by
      have := Nat.mul_le_mul_right p.n (show r + 1 ≤ p.a by omega_using [h₂]); rw [Nat.succ_mul] at this
      omega_using [this, han]
    have hsr : s p.a * p.n ≤ r * p.n := Nat.mul_le_mul_right _ h₁
    rw [Levels.add_add, bytesAt_frame f₄ (dN _ _ hrn) (by omega_using [hn32]),
      bytesAt_frame H.frame (dSub _ _ hrn (.inr (by omega_using [hsr]))) (by omega_using [hn32]),
      bytesAt_frame L₂.frame (dLoop _ _ hrn (by omega_using [])) (by omega_using [hn32]),
      bytesAt_frame f₁ (dF _ _ hrn) (by omega_using [hn32]), ← Levels.add_add]
    exact hI.high r h₁ h₂
  · -- the subtree roots
    have hun : u' * p.n + p.n ≤ 32 * p.n := by
      have := Nat.mul_le_mul_right p.n (show u' + 1 ≤ 32 by omega_using [hu', hu, hU]); rw [Nat.succ_mul] at this; exact this
    have eR : Layout.oRoots = 29280 := rfl
    have eN' : Layout.oN = 12640 := rfl
    have eNS' : Layout.nodeSlots = 520 := rfl
    by_cases e : u' = u
    · subst e
      rw [keepSB f₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact dS S (.inr (by rw [oVar2, eR]; omega_using [])) (by rw [eR]; omega_using [hun, hn32]) (by rw [oVar2]; omega_using []))
        (by omega_using [hn32])]
      have hroot := H.root
      rw [hR, div_add_dvd hdv4, hR, mul_pow_div tt hsa, hr12₂] at hroot
      exact hroot
    · have hlt : u' < u := by omega_using [hu', e]
      have hul : u' * p.n + p.n ≤ u * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hlt
      rw [← hI.roots u' hlt]
      refine bytesAt_ext fun i hi => ?_
      rw [Levels.add_add, k24 _ (by rw [eR]; omega_using [hun, hi, hn32]) (by rw [eR]; omega_using [])
        (.inr (by rw [eR]; omega_using [])) (.inr (by rw [eR]; omega_using [])) (.inr (by rw [eR]; omega_using []))
        (fun k hk => .inr (by rw [laneA_eq, eR]; omega_using [hk, hn32])) (.inr (by rw [eR, eN']; omega_using [hc520]))
        (.inl (by rw [hR]; omega_using [hul, hi]))]
      refine (keepS L₂.frame fun r hr => ?_).trans (keepS f₁ fun r hr => ?_)
      · exact dW hn32 hAUd (by rw [hsp₁]; exact C.stk)
          (by rw [eR]; omega_using [hun, hi, hn32]) (by rw [eR]; omega_using []) (.inr (by rw [eR]; omega_using []))
          (.inr (by rw [oVar2, eR]; omega_using [])) (.inr (by rw [eR, eN', eNS']; omega_using []))
          (by rw [oVar2]; omega_using []) (by rw [eN', eNS']; omega_using [])
          (fun k hk => .inr (by rw [laneA_eq, eR]; omega_using [hk, hn32])) r hr
      · simp only [List.mem_singleton] at hr; subst hr
        exact dS S (.inr (by rw [oVar2, eR]; omega_using [])) (by rw [eR]; omega_using [hun, hi, hn32]) (by rw [oVar2]; omega_using [])
  · -- the frame
    have mem : ∀ {x : Region}, x ∈ subW p S AU (t₀.gpr .rsp) stack → ∃ r' ∈ subW p S AU (t₀.gpr .rsp) stack, Region.Sub x r' :=
      fun h => ⟨_, h, fun _ h => h⟩
    have tail : ∀ k < 4, (⟨at' S (Layout.laneA k + p.n + 16), 16 + 2 * p.n⟩ : Region) ∈ subW p S AU (t₀.gpr .rsp) stack :=
      fun k hk => List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
    refine hI.frame.trans ((f₁.sub fun x hx => ?_).trans ((L₂.frame.sub fun x hx => ?_).trans
      ((H.frame.sub fun x hx => ?_).trans (f₄.sub fun x hx => ?_))))
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨⟨at' S (Layout.oVar 2 2), 16⟩, by simp, Offset.sub S (by decide) (by decide)⟩
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, laneRs, List.mem_map, List.mem_range] at hx
      rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨k, hk, rfl⟩
      · exact mem (by simp)
      · exact mem (by simp)
      · exact ⟨⟨at' S (Layout.oVar 2 2), 16⟩, by simp, Offset.sub S (by decide) (by decide)⟩
      · exact mem (by simp)
      · exact ⟨⟨AU, (p.a + 1) * p.n⟩, by simp, Region.sub_prefix (by omega_using [han])⟩
      · rw [hsp₁]; exact mem (by simp)
      · exact ⟨_, tail k hk, Offset.sub S (by omega_using []) (by omega_using [])⟩
    · rcases List.mem_append.mp hx with hx | hx
      · simp only [levelsChanges, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
          or_false] at hx
        rcases hx with ⟨k, hk, rfl⟩ | rfl | rfl | rfl | rfl
        · exact ⟨_, tail k hk, fun _ h => h⟩
        · exact mem (by simp)
        · exact mem (by simp)
        · exact mem (by simp)
        · exact ⟨⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩, by simp, Offset.sub S (by omega_using [])
            (by rw [show Layout.nodeSlots = 520 from rfl]; omega_using [hc520])⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨⟨AU, (p.a + 1) * p.n⟩, by simp, Offset.sub_base AU (by omega_using [han, hsn])⟩
        · rw [hsp₂]; exact mem (by simp)
        · exact ⟨⟨at' S Layout.oRoots, 1024⟩, by simp, Offset.sub S (by omega_using [])
            (by rw [show Layout.oRoots = 29280 from rfl] at *; omega_using [hslot])⟩
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨⟨at' S (Layout.oVar 2 2), 16⟩, by simp, Offset.sub S (by decide) (by decide)⟩

/-- The loop of the subtrees of a tree, from subtree `u` on. -/
theorem subs_ok {p : Params} (T : Thash4Impl p.n) (name ln : String) {stack : Nat} (hst : T.stack + 24 ≤ stack)
    (hs63 : stack < 2 ^ 63) {S SG AU : Addr} {L dA tt idx : Nat} {pkSeed a16 skSeed : List Byte} {t₀ : State}
    (C : SC p stack S SG AU L dA tt idx t₀) {u m : Nat} {t : State} (hm : 0 < m) (hum : u + m = 2 ^ (p.a - s p.a))
    (hI : ST p stack S AU pkSeed a16 skSeed (t₀.gpr .r12).toNat tt idx t₀ u t) :
    WP isa (.loop (subtreeBody ⟨p.n, p.len⟩ p.a name ln T.code) .ne) t
      (ST p stack S AU pkSeed a16 skSeed (t₀.gpr .r12).toNat tt idx t₀ (2 ^ (p.a - s p.a))) := by
  have hUs : 2 ^ (p.a - s p.a) * 2 ^ s p.a = 2 ^ p.a := by rw [← Nat.pow_add, Nat.sub_add_cancel (s_le p.a)]
  let I : Nat → State → Prop := fun m v => ∃ u, u + m = 2 ^ (p.a - s p.a) ∧ 0 < m ∧
    ST p stack S AU pkSeed a16 skSeed (t₀.gpr .r12).toNat tt idx t₀ u v
  refine Levels.wpLoop (I := I) (fun m => decide (1 < m)) (fun m => m - 1) (fun m v ⟨u, hu, hm, H⟩ => ?_) m ⟨u, hum, hm, hI⟩
  refine WP.mono (sub_ok T name ln hst hs63 C (by omega_using [hu, hm]) H) fun v' ⟨hz, H'⟩ => ?_
  have hiff : (u + 1) * 2 ^ s p.a = 2 ^ p.a ↔ ¬ 1 < m := by
    rw [← hUs]
    constructor
    · intro e; have := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) e; omega_using [this, hu]
    · intro e; rw [show u + 1 = 2 ^ (p.a - s p.a) by omega_using [e, hu, hm]]
  refine ⟨by rw [eval_ne hz]; congr 1; by_cases h : 1 < m <;> simp [h, hiff], fun hc => ?_, fun hc => ?_⟩
  · have := of_decide_eq_false hc
    rw [show 2 ^ (p.a - s p.a) = u + 1 by omega_using [this, hu, hm]]; exact H'
  · have := of_decide_eq_true hc
    exact ⟨by omega_using [this], u + 1, by omega_using [hu, this], by omega_using [this], H'⟩

end VG.Proof.SlhDsa.X86_64.Fors
