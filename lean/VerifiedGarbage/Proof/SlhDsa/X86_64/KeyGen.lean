module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.KeyGenPro
public import VerifiedGarbage.Spec.SlhDsa.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsMain
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsBlocks

/-!
# SLH-DSA (SHAKE) on x86-64: key generation, correct

`keygen(seeds = rdi, sk = rsi, pk = rdx, scratch = rcx)`
(`Impl.SlhDsa.X86_64.Shake.keyGen`): the prologue (`KeyGenPro.lean`), the
call of `xmssTree` on the top layer's tree with no key pair to sign with
(`xmsscall_ok`), whose root is `PK.root`, then the keys copied out and the
callee-saved registers restored (`tail_ok`): `slh_keygen_internal`
(Algorithm 18), as `kgK` states it (`keyGen_wp`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.KeyGen

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout savedRegs copyWords)
open VG.Impl.SlhDsa.X86_64.Shake (oKgSave kgSave kgRestore writeKeys)
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_addi wp_mov32i wp_store ea_at)
open VG.Proof.SlhDsa.X86_64.Levels (in_scr in_scr' at_add disj_scr scr0)

/-! ## The contract, as the proof uses it -/

/-- `keyGenContract`'s precondition, a fact at a time. -/
structure KG (p : Params) (stack : Nat) (s : State) : Prop where
  sp : stack ≤ (s.gpr .rsp).toNat
  rd : s.rd = [⟨s.gpr .rdi, 3 * p.n⟩]
  wr : s.wr = [⟨s.gpr .rsi, p.skLen⟩, ⟨s.gpr .rdx, p.pkLen⟩, ⟨s.gpr .rcx, scratchLen⟩]
  d_seed_sk : Region.Disjoint ⟨s.gpr .rdi, 3 * p.n⟩ ⟨s.gpr .rsi, p.skLen⟩
  d_seed_pk : Region.Disjoint ⟨s.gpr .rdi, 3 * p.n⟩ ⟨s.gpr .rdx, p.pkLen⟩
  d_seed_scr : Region.Disjoint ⟨s.gpr .rdi, 3 * p.n⟩ ⟨s.gpr .rcx, scratchLen⟩
  d_sk_pk : Region.Disjoint ⟨s.gpr .rsi, p.skLen⟩ ⟨s.gpr .rdx, p.pkLen⟩
  d_sk_scr : Region.Disjoint ⟨s.gpr .rsi, p.skLen⟩ ⟨s.gpr .rcx, scratchLen⟩
  d_pk_scr : Region.Disjoint ⟨s.gpr .rdx, p.pkLen⟩ ⟨s.gpr .rcx, scratchLen⟩
  ret_sk : (retR s).Disjoint ⟨s.gpr .rsi, p.skLen⟩
  ret_pk : (retR s).Disjoint ⟨s.gpr .rdx, p.pkLen⟩
  ret_scr : (retR s).Disjoint ⟨s.gpr .rcx, scratchLen⟩
  stk_sk : (below (s.gpr .rsp) stack).Disjoint ⟨s.gpr .rsi, p.skLen⟩
  stk_pk : (below (s.gpr .rsp) stack).Disjoint ⟨s.gpr .rdx, p.pkLen⟩
  stk_scr : (below (s.gpr .rsp) stack).Disjoint ⟨s.gpr .rcx, scratchLen⟩
  f_seed : (s.gpr .rdi).toNat + 3 * p.n ≤ 2 ^ 64
  f_sk : (s.gpr .rsi).toNat + p.skLen ≤ 2 ^ 64
  f_pk : (s.gpr .rdx).toNat + p.pkLen ≤ 2 ^ 64
  f_scr : (s.gpr .rcx).toNat + scratchLen ≤ 2 ^ 64

/-- The keys of `slh_keygen_internal` of the seeds at `rdi`. -/
abbrev kgOut (p : Params) (s : State) : List Byte × List Byte :=
  let x := bytesAt s.mem (s.gpr .rdi) (3 * p.n)
  keyGenInternal p (chunk x p.n 0) (chunk x p.n 1) (chunk x p.n 2)

def kgK (p : Params) (stack : Nat) : Contract isa where
  pre s := KG p stack s
  post s s' := (bytesAt s'.mem (s.gpr .rsi) p.skLen, bytesAt s'.mem (s.gpr .rdx) p.pkLen) = kgOut p s
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-! ## Bytes -/

theorem bytesAt_add (m : Mem) (a : Addr) (x y : Nat) :
    bytesAt m a (x + y) = bytesAt m a x ++ bytesAt m (a + BitVec.ofNat 64 x) y := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- String `z` of the `c` strings of `n` bytes at `a`. -/
theorem chunk_bytesAt (m : Mem) (a : Addr) {n z c : Nat} (hz : z < c) :
    chunk (bytesAt m a (c * n)) n z = bytesAt m (a + BitVec.ofNat 64 (n * z)) n := by
  have hl : (chunk (bytesAt m a (c * n)) n z).length = n := by
    simp only [chunk, List.length_take, List.length_drop, bytesAt, List.length_map, List.length_range]
    have : n ≤ c * n - n * z := by
      rw [Nat.mul_comm n z, ← Nat.sub_mul]
      exact Nat.le_mul_of_pos_left n (by omega)
    omega
  apply List.ext_getElem (by rw [hl]; simp [bytesAt])
  intro i h₁ h₂
  have hi : i < n := by rw [hl] at h₁; exact h₁
  have hzn : n * z + i < c * n := by
    have : n * z + n ≤ c * n := by rw [Nat.mul_comm c n, ← Nat.mul_succ]; exact Nat.mul_le_mul_left n hz
    omega
  simp only [chunk, List.getElem_take, List.getElem_drop, bytesAt, List.getElem_map, List.getElem_range]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## Copies out -/

/-- After `c` of `K` copies of `n` bytes from `scratch + o + 32 c` to `D + n c`. -/
def OutI (n : Nat) (s : State) (S D : Addr) (o K c : Nat) (t : State) : Prop :=
  (∀ g, g ≠ .rax → t.gpr g = s.gpr g) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    (∀ c' < c, bytesAt t.mem (D + BitVec.ofNat 64 (n * c')) n = bytesAt s.mem (at' S (o + 32 * c')) n) ∧
    Frame [⟨D, K * n⟩] s.mem t.mem

theorem out_ok {n : Nat} (hn : n ≤ 32) (h8 : n % 8 = 0) {s : State} {S D : Addr} {r : Reg} (hr : r ≠ .rax)
    {o K : Nat} (hK : K ≤ 4) (ho : o + 32 * K ≤ 2 ^ 16)
    (hb : s.gpr .rbx = S) (hd : s.gpr r = D) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (hwD : (⟨D, K * n⟩ : Region) ∈ s.wr)
    (hDf : D.toNat + K * n ≤ 2 ^ 64) (hdis : Region.Disjoint ⟨D, K * n⟩ ⟨S, 2 ^ 16⟩) :
    WP isa (.block ((List.range K).flatMap fun c => copyWords r (n * c) .rbx (o + 32 * c) (n / 8))) s
      (OutI n s S D o K K) := by
  have h8n : 8 * (n / 8) = n := by omega
  have hnK : n * K ≤ 128 := Nat.mul_le_mul hn hK
  refine wp_flatMap (P := OutI n s S D o K) K ⟨fun _ _ => rfl, rfl, rfl, fun _ h => absurd h (by omega), Frame.refl _ _⟩
    fun c hc t ⟨hg, rd, w, kc, f⟩ => ?_
  have hbt : t.gpr .rbx = S := by rw [hg _ (by decide), hb]
  have hdt : t.gpr r = D := by rw [hg _ hr, hd]
  have hnc : n * c + n ≤ n * K := by
    have := Nat.mul_le_mul_left n (show c + 1 ≤ K by omega); rwa [Nat.mul_succ] at this
  have hD : ∀ {o' l : Nat}, o' + l ≤ K * n → Region.Disjoint ⟨D + BitVec.ofNat 64 o', l⟩ ⟨S, 2 ^ 16⟩ :=
    fun {o' l} h => hdis.sub_left (Offset.sub_base D h)
  refine WP.mono (copyWords_ok (s := t) (t := r) (src := .rbx) hr (by decide)
    (d₂ := n * c) (d₁ := o + 32 * c) (w := n / 8)
    (fun j hj => by
      rw [w, hdt]
      exact ⟨_, hwD, Offset.contains_base _ (by rw [Nat.mul_comm K n]; omega) (by omega)⟩)
    (fun j hj => by rw [rd, w, hbt]; exact in_scr' hw (by omega))
    (by
      rw [hbt, hdt, h8n]
      exact (hD (o' := n * c) (l := n) (by rw [Nat.mul_comm K n]; omega)).sub_right
        (Offset.sub_base S (by omega)))
    (by omega) (by omega)) fun u cp => ?_
  rw [hbt, hdt, h8n] at cp
  have hcs : bytesAt u.mem (D + BitVec.ofNat 64 (n * c)) n = bytesAt s.mem (at' S (o + 32 * c)) n := by
    rw [bytesAt_eq_of (m' := t.mem) (b := S + BitVec.ofNat 64 (o + 32 * c)) fun q hq => cp.bytes q hq]
    exact bytesAt_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hdis.sub_right (Offset.sub_base S (by omega))).symm) (by omega)
  refine ⟨fun g h => by rw [cp.gpr _ h, hg _ h], by rw [cp.rd, rd], by rw [cp.wr, w], fun c' hc' => ?_, ?_⟩
  · by_cases e : c' = c
    · subst e; exact hcs
    · have : n * c' + n ≤ n * K := by
        have := Nat.mul_le_mul_left n (show c' + 1 ≤ K by omega); rwa [Nat.mul_succ] at this
      rw [bytesAt_frame cp.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint D (by
          rcases Nat.lt_or_gt_of_ne e with h | h
          · have := Nat.mul_le_mul_left n (show c' + 1 ≤ c by omega); left; rw [Nat.mul_succ] at this; omega
          · have := Nat.mul_le_mul_left n (show c + 1 ≤ c' by omega); right; rw [Nat.mul_succ] at this; omega)
          (by omega) (by omega)) (by omega)]
      exact kc c' (by omega)
  · exact f.trans (cp.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base D (by rw [Nat.mul_comm K n]; omega)⟩)

/-! ## The callee-saved registers -/

theorem restore_ok {σ t : State} {S : Addr} (hbx : t.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr)
    (hsv : ∀ i < 6, t.mem.readW (at' S (oKgSave + 8 * i)) 64 = σ.gpr (savedRegs.getD i .rbx))
    (hsp : t.gpr .rsp = σ.gpr .rsp) {Q : State → Prop}
    (k : ∀ t', t'.mem = t.mem → t'.rd = t.rd → t'.wr = t.wr → (∀ r ∈ calleeSaved, t'.gpr r = σ.gpr r) → Q t') :
    WP isa (.block (kgRestore)) t Q := by
  have hin : ∀ (u : State), u.rd = t.rd → u.wr = t.wr → ∀ i < 6, InRegions (u.rd ++ u.wr) (at' S (oKgSave + 8 * i)) 8 :=
    fun u hr hw' i hi => by rw [hr, hw']; exact in_scr' hw (by rw [show oKgSave = 34080 from rfl]; omega)
  rw [show kgRestore = [Instr.mov .r15 (.mem (Impl.Sha3.X86_64.at_ .rbx (oKgSave + 8 * 5))),
    .mov .r14 (.mem (Impl.Sha3.X86_64.at_ .rbx (oKgSave + 8 * 4))), .mov .r13 (.mem (Impl.Sha3.X86_64.at_ .rbx (oKgSave + 8 * 3))),
    .mov .r12 (.mem (Impl.Sha3.X86_64.at_ .rbx (oKgSave + 8 * 2))), .mov .rbp (.mem (Impl.Sha3.X86_64.at_ .rbx (oKgSave + 8 * 1))),
    .mov .rbx (.mem (Impl.Sha3.X86_64.at_ .rbx (oKgSave + 8 * 0)))] from rfl]
  refine wp_movm (by rw [ea_at, hbx]) (hin t rfl rfl 5 (by decide)) fun t₁ u₁ => ?_
  refine wp_movm (by rw [ea_at, u₁.other _ (by decide), hbx]) (hin _ u₁.rd u₁.wr 4 (by decide)) fun t₂ u₂ => ?_
  refine wp_movm (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) 3 (by decide)) fun t₃ u₃ => ?_
  refine wp_movm (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr]) 2 (by decide)) fun t₄ u₄ => ?_
  refine wp_movm (by rw [ea_at, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 1 (by decide)) fun t₅ u₅ => ?_
  refine wp_movm (by rw [ea_at, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 0 (by decide))
    fun t₆ u₆ => WP.block_nil ?_
  have hm₁ : t₁.mem = t.mem := u₁.mem
  have hm₂ : t₂.mem = t.mem := by rw [u₂.mem, hm₁]
  have hm₃ : t₃.mem = t.mem := by rw [u₃.mem, hm₂]
  have hm₄ : t₄.mem = t.mem := by rw [u₄.mem, hm₃]
  have hm₅ : t₅.mem = t.mem := by rw [u₅.mem, hm₄]
  refine k t₆ (by rw [u₆.mem, hm₅]) (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) fun r hr => ?_
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [u₆.gpr, hm₅]; exact hsv 0 (by decide)
  · rw [u₆.other _ (by decide), u₅.gpr, hm₄]; exact hsv 1 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hsp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, hm₃]; exact hsv 2 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, hm₂]
    exact hsv 3 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hm₁]
    exact hsv 4 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
    exact hsv 5 (by decide)


/-! ## The tail: the keys out -/

theorem bytesAt_four (m : Mem) (a : Addr) (n : Nat) :
    bytesAt m a (4 * n) = bytesAt m (a + BitVec.ofNat 64 (n * 0)) n ++ bytesAt m (a + BitVec.ofNat 64 (n * 1)) n ++
      bytesAt m (a + BitVec.ofNat 64 (n * 2)) n ++ bytesAt m (a + BitVec.ofNat 64 (n * 3)) n := by
  rw [show 4 * n = n + (n + (n + n)) by omega, bytesAt_add, bytesAt_add, bytesAt_add]
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, List.append_assoc, Nat.mul_zero, Nat.mul_one, BitVec.add_zero]
  rw [show n + n = n * 2 by omega, show n * 2 + n = n * 3 by omega]

theorem bytesAt_two (m : Mem) (a : Addr) (n : Nat) :
    bytesAt m a (2 * n) = bytesAt m (a + BitVec.ofNat 64 (n * 0)) n ++ bytesAt m (a + BitVec.ofNat 64 (n * 1)) n := by
  rw [show 2 * n = n + n by omega, bytesAt_add]
  simp only [Nat.mul_zero, Nat.mul_one, BitVec.add_zero]

/-- The last block of `keyGen`. -/
abbrev tailCode (p : Params) : List Instr :=
  copyWords .rbx Layout.oPkRoot .rbx Layout.oMsg (p.n / 8) ++ writeKeys p ++ kgRestore

theorem tail_ok {p : Params} (hn : p.n ≤ 32) (h8 : p.n % 8 = 0) {σ w : State} {S SK PK : Addr}
    (hb : w.gpr .rbx = S) (h12 : w.gpr .r12 = SK) (h13 : w.gpr .r13 = PK) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ w.wr)
    (hsk : (⟨SK, 4 * p.n⟩ : Region) ∈ w.wr) (hpk : (⟨PK, 2 * p.n⟩ : Region) ∈ w.wr)
    (fsk : SK.toNat + 4 * p.n ≤ 2 ^ 64) (fpk : PK.toNat + 2 * p.n ≤ 2 ^ 64)
    (dsk : Region.Disjoint ⟨SK, 4 * p.n⟩ ⟨S, 2 ^ 16⟩) (dpk : Region.Disjoint ⟨PK, 2 * p.n⟩ ⟨S, 2 ^ 16⟩)
    (dskpk : Region.Disjoint ⟨SK, 4 * p.n⟩ ⟨PK, 2 * p.n⟩)
    (hsv : ∀ i < 6, w.mem.readW (at' S (oKgSave + 8 * i)) 64 = σ.gpr (savedRegs.getD i .rbx))
    (hsp : w.gpr .rsp = σ.gpr .rsp) {Q : State → Prop}
    (k : ∀ t, t.rd = w.rd → t.wr = w.wr → (∀ r ∈ calleeSaved, t.gpr r = σ.gpr r) →
      bytesAt t.mem SK (4 * p.n) = bytesAt w.mem (at' S Layout.oKeys) p.n ++
        bytesAt w.mem (at' S (Layout.oKeys + 32)) p.n ++ bytesAt w.mem (at' S (Layout.oKeys + 64)) p.n ++
        bytesAt w.mem (at' S Layout.oMsg) p.n →
      bytesAt t.mem PK (2 * p.n) = bytesAt w.mem (at' S (Layout.oKeys + 64)) p.n ++
        bytesAt w.mem (at' S Layout.oMsg) p.n →
      Frame [⟨at' S Layout.oPkRoot, p.n⟩, ⟨SK, 4 * p.n⟩, ⟨PK, 2 * p.n⟩] w.mem t.mem → Q t) :
    WP isa (.block (tailCode p)) w Q := by
  have eK : Layout.oKeys = 3168 := rfl
  have eR : Layout.oPkRoot = 3264 := rfl
  have eM : Layout.oMsg = 30496 := rfl
  have h8n : 8 * (p.n / 8) = p.n := by omega
  simp only [tailCode, writeKeys, List.append_assoc]
  refine WP.block_append (copyS_ok hb hw (d₁ := Layout.oMsg) (d₂ := Layout.oPkRoot) (w := p.n / 8)
    (by rw [eM]; omega) (by rw [eR]; omega) (by rw [eM, eR]; omega) fun t₁ g₁ r₁ w₁ b₁ f₁ => ?_)
  rw [h8n] at b₁ f₁
  have hk₁ : ∀ c < 3, bytesAt t₁.mem (at' S (Layout.oKeys + 32 * c)) p.n = bytesAt w.mem (at' S (Layout.oKeys + 32 * c)) p.n :=
    fun c hc => bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact disj_scr S (by rw [eK, eR]; omega) (by omega) (by omega))
      (by omega)
  have hbt : t₁.gpr .rbx = S := by rw [g₁ _ (by decide), hb]
  refine WP.block_append (WP.mono (out_ok (r := .r12) hn h8 (by decide) (o := Layout.oKeys) (K := 4) (by decide)
    (by rw [eK]; omega) hbt (by rw [g₁ _ (by decide), h12]) (by rw [w₁]; exact hw) (by rw [w₁]; exact hsk) fsk dsk)
    fun t₂ ⟨g₂, r₂, w₂, o₂, f₂⟩ => ?_)
  have hbt₂ : t₂.gpr .rbx = S := by rw [g₂ _ (by decide), hbt]
  refine WP.block_append (WP.mono (out_ok (r := .r13) hn h8 (by decide) (o := Layout.oKeys + 64) (K := 2) (by decide)
    (by rw [eK]; omega) hbt₂ (by rw [g₂ _ (by decide), g₁ _ (by decide), h13]) (by rw [w₂, w₁]; exact hw)
    (by rw [w₂, w₁]; exact hpk) fpk dpk) fun t₃ ⟨g₃, r₃, w₃, o₃, f₃⟩ => ?_)
  have hbt₃ : t₃.gpr .rbx = S := by rw [g₃ _ (by decide), hbt₂]
  -- the scratch's words are unchanged by the copies out
  have hsc : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 →
      bytesAt t₃.mem (at' S o) l = bytesAt t₁.mem (at' S o) l := fun {o l} h => by
    rw [bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dpk.sub_right (Levels.sub_scr S h)).symm) (by omega),
      bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dsk.sub_right (Levels.sub_scr S h)).symm) (by omega)]
  refine restore_ok (σ := σ) hbt₃ (by rw [w₃, w₂, w₁]; exact hw) (fun i hi => ?_)
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hsp]) fun t hm hr hw' hcs => ?_
  · have d : ∀ r ∈ [(⟨at' S Layout.oPkRoot, p.n⟩ : Region)], Region.Disjoint ⟨at' S (oKgSave + 8 * i), 8⟩ r :=
      fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact disj_scr S (by rw [eR, show oKgSave = 34080 from rfl]; omega) (by rw [show oKgSave = 34080 from rfl]; omega)
          (by omega)
    have hs16 : oKgSave + 8 * i + 8 ≤ 2 ^ 16 := by rw [show oKgSave = 34080 from rfl]; omega
    rw [Thash4Avx.readW_frame f₃ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dpk.sub_right (Levels.sub_scr S hs16)).symm,
      Thash4Avx.readW_frame f₂ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dsk.sub_right (Levels.sub_scr S hs16)).symm,
      Thash4Avx.readW_frame f₁ d]
    exact hsv i hi
  · have hsk3 : ∀ c < 4, bytesAt t₃.mem (SK + BitVec.ofNat 64 (p.n * c)) p.n = bytesAt t₁.mem (at' S (Layout.oKeys + 32 * c)) p.n :=
      fun c hc => by
        have : p.n * c + p.n ≤ 4 * p.n := by
          have := Nat.mul_le_mul_left p.n (show c + 1 ≤ 4 by omega); rw [Nat.mul_succ] at this; omega
        rw [bytesAt_frame f₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact dskpk.sub_left (Offset.sub_base SK this)) (by omega)]
        exact o₂ c hc
    have hpk2 : ∀ c < 2, bytesAt t₃.mem (PK + BitVec.ofNat 64 (p.n * c)) p.n =
        bytesAt t₁.mem (at' S (Layout.oKeys + 64 + 32 * c)) p.n := fun c hc => by
      rw [o₃ c hc]
      exact bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dsk.sub_right (Levels.sub_scr S (by rw [eK]; omega))).symm) (by omega)
    refine k t (by rw [hr, r₃, r₂, r₁]) (by rw [hw', w₃, w₂, w₁]) hcs ?_ ?_ ?_
    · rw [hm, bytesAt_four, hsk3 0 (by decide), hsk3 1 (by decide), hsk3 2 (by decide), hsk3 3 (by decide),
        hk₁ 0 (by decide), hk₁ 1 (by decide), hk₁ 2 (by decide), show Layout.oKeys + 32 * 3 = Layout.oPkRoot from rfl, b₁]
      rfl
    · rw [hm, bytesAt_two, hpk2 0 (by decide), hpk2 1 (by decide),
        show Layout.oKeys + 64 + 32 * 0 = Layout.oKeys + 32 * 2 from rfl, hk₁ 2 (by decide),
        show Layout.oKeys + 64 + 32 * 1 = Layout.oPkRoot from rfl, b₁]
    · rw [hm]
      refine (f₁.mono fun r hr => ?_).trans ((f₂.mono fun r hr => ?_).trans (f₃.mono fun r hr => ?_)) <;>
        simp only [List.mem_singleton] at hr <;> subst hr <;> simp


/-! ## The call of `xmssTree` -/

theorem sigLen_le {p : Params} (hz : Wots4.Sz p) (hh : XmssTree.Hps p.hp) : p.xmssSigLen ≤ 2432 := by
  rcases hz.nv with e | e | e <;> rcases hh with h | h | h | h <;>
    (simp only [Params.xmssSigLen, hz.len, e, h]; decide)

/-- The regions of the call: `scratch` and the signature it discards. -/
abbrev callW (p : Params) (S : Addr) : List Region :=
  [⟨S, scratchLen⟩, ⟨at' S Layout.oSigTmp, p.xmssSigLen⟩]

theorem call_pre {p : Params} (hz : Wots4.Sz p) (hh : XmssTree.Hps p.hp) {stack : Nat} (hst : 32 ≤ stack)
    (hs63 : stack < 2 ^ 63) {σ u : State} {S X : Addr} (hK : KG p stack σ) (hS : σ.gpr .rcx = S)
    (hu : KPro p σ S X u) :
    (xmssContract p (stack - 8)).pre (u.callEntry.withRegions [] (callW p S)) ∧
      Covers ([] ++ callW p S) (u.rd ++ u.wr) ∧ Covers (callW p S) u.wr := by
  have hL := sigLen_le hz hh
  have eT : Layout.oSigTmp = 31648 := rfl
  have hn32 := hz.n32
  have fS : S.toNat + scratchLen ≤ 2 ^ 64 := by rw [← hS]; exact hK.f_scr
  have dS : (below (σ.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩ := by rw [← hS]; exact hK.stk_scr
  have hsig : Region.Sub ⟨at' S Layout.oSigTmp, p.xmssSigLen⟩ ⟨S, 2 ^ 16⟩ := Levels.sub_scr S (by omega)
  have hg : ∀ r, r ≠ .rsp → (u.callEntry.withRegions [] (callW p S)).gpr r = u.gpr r :=
    fun r h => by rw [State.withRegions_gpr, State.callEntry_gpr _ h]
  have hret : retR (u.callEntry.withRegions [] (callW p S)) = below (σ.gpr .rsp) 8 := by
    simp [retR, State.callEntry_rsp, hu.sp]
  have h8 : Region.Sub (below (σ.gpr .rsp) 8) (below (σ.gpr .rsp) stack) := below_sub (by omega) (by omega)
  have hc : Region.Sub (below ((u.callEntry.withRegions [] (callW p S)).gpr .rsp) (stack - 8))
      (below (σ.gpr .rsp) stack) := by
    simp only [State.withRegions_gpr, State.callEntry_rsp, hu.sp]
    exact fun x hx => below_sub (sp := σ.gpr .rsp) (a := stack - 8 + 8) (by omega) (by omega) x
      (below_callee _ _ x hx)
  have hcov : Covers (callW p S) u.wr := Covers.of_sub fun r hr => by
    rw [hu.wr, hK.wr, hS]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), 0, scr0 S, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Layout.oSigTmp, rfl,
        by simp only [scratchLen]; omega⟩
  refine ⟨⟨?_, ⟨bytesAt σ.mem (X + BitVec.ofNat 64 (p.n * 2)) p.n, Proof.SlhDsa.layerTree (p.d - 1) 0, ?_⟩, ?_⟩, by rw [List.nil_append]; exact Covers.right hcov, hcov⟩
  · rw [hg _ (by decide), hg _ (by decide), hu.rdi, hu.rdx]
    refine ⟨rfl, rfl, fS, ?_, Offset.disjoint_base S (by omega) (by omega), fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil, ?_, ?_, fun _ h => absurd h List.not_mem_nil, ?_, ?_,
      fun _ h => absurd h List.not_mem_nil⟩
    · show (at' S Layout.oSigTmp).toNat + p.xmssSigLen ≤ 2 ^ 64
      rw [Levels.toNat_at (by simp only [scratchLen] at fS; omega)]; simp only [scratchLen] at fS; omega
    · rw [hret]; exact dS.sub_left h8
    · rw [hret]; exact (dS.sub_left h8).sub_right hsig
    · exact dS.sub_left hc
    · exact (dS.sub_left hc).sub_right hsig
  · rw [hg _ (by decide), hu.rdi, State.withRegions_mem]
    exact Env.of_frame hn32 hu.env ((XmssTree.frame_callEntry u).mono fun r hr => List.mem_append_right _ hr)
      (by rw [hu.sp]; exact dS.sub_left h8)
  · rw [hg _ (by decide), hu.rsi]; decide

/-- The root of the top layer's tree, at the address the code sets. -/
theorem root_adrs (p : Params) (skSeed pkSeed : List Byte) :
    xmssNode p skSeed 0 p.hp pkSeed (treeAdrs (Proof.SlhDsa.layerTree (p.d - 1) 0)) =
      xmssNode p skSeed 0 p.hp pkSeed (setLayerAddress adrsZero (p.d - 1)) := by
  refine Proof.SlhDsa.xmssNode_congr (p := p) skSeed pkSeed ?_ ?_ ?_ p.hp 0
  · simp [treeAdrs, Proof.SlhDsa.layerTree, toByte]
  · simp [setLayerAddress, setBytes, adrsZero, toByte]
  · simp [treeAdrs, Proof.SlhDsa.layerTree, setLayerAddress, setBytes, adrsZero, toByte_zero, toByte_length]


/-- The keys are outside what the internal functions change. -/
theorem keys_disj {p : Params} (hn32 : p.n ≤ 32) (S : Addr) {o l : Nat} (h₁ : Layout.oKeys ≤ o)
    (h₂ : o + l ≤ Layout.oA) : ∀ r ∈ changes p S, Region.Disjoint ⟨at' S o, l⟩ r := by
  have eK : Layout.oKeys = 3168 := rfl
  have eA : Layout.oA = 3296 := rfl
  intro r hr
  simp only [changes, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil,
    or_false] at hr
  rcases hr with ((h | h | h) | ⟨k, hk, h | h⟩) | (h | h | h | h | h) <;> subst h
  · have h := disj_scr (o' := 0) (l' := 1600) S (o := o) (l := l) (by omega) (by omega) (by omega)
    simpa using h
  · exact disj_scr S (by omega) (by omega) (by omega)
  · exact disj_scr S (by rw [show Layout.oVars = 2400 from rfl]; omega) (by omega) (by rw [show Layout.oVars = 2400 from rfl]; omega)
  · exact disj_scr S (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega) (by omega)
      (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega)
  · exact disj_scr S (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega) (by omega)
      (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega)
  · exact disj_scr S (by rw [show Layout.oDigits = 30368 from rfl]; omega) (by omega) (by rw [show Layout.oDigits = 30368 from rfl]; omega)
  · exact disj_scr S (by rw [show Layout.oN = 12640 from rfl]; omega) (by omega)
      (by rw [show Layout.oN = 12640 from rfl, show Layout.nodeSlots = 520 from rfl]; omega)
  · exact disj_scr S (by rw [show Layout.oRoots = 29280 from rfl]; omega) (by omega) (by rw [show Layout.oRoots = 29280 from rfl]; omega)
  · exact disj_scr S (by rw [show Layout.oMsg = 30496 from rfl]; omega) (by omega) (by rw [show Layout.oMsg = 30496 from rfl]; omega)
  · exact disj_scr S (by rw [show Layout.oFidx = 31328 from rfl]; omega) (by omega) (by rw [show Layout.oFidx = 31328 from rfl]; omega)


/-! ## The function -/

theorem pro_nm (p : Params) : (Code.block (proCode p) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp [Code.allInstrs_eq, instrs, proCode, kgSave, Impl.SlhDsa.X86_64.Shake.rcTable,
    Impl.SlhDsa.X86_64.Shake.seedLanes, Impl.SlhDsa.X86_64.Shake.treeLanes, Impl.SlhDsa.X86_64.setField,
    Impl.SlhDsa.X86_64.setFieldR, copyWords, List.all_flatMap, List.all_map, loadsMxcsr]

theorem tail_nm (p : Params) : (Code.block (tailCode p) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp [Code.allInstrs_eq, instrs, tailCode, writeKeys, kgRestore, copyWords, List.all_flatMap, List.all_map,
    loadsMxcsr]

/-- `Impl.SlhDsa.X86_64.Shake.keyGen` from `kgK`'s precondition: its postcondition and the calling convention. -/
theorem keyGen_wp {p : Params} (hz : Wots4.Sz p) (hh : XmssTree.Hps p.hp) (hd : p.d - 1 < 2 ^ 31)
    (T : Thash4Impl p.n) {f : Impl.SlhDsa.X86_64.Shake.Fns} (ht : f.t4 = T.code) {stack : Nat}
    (hst : T.stack + 32 ≤ stack) (hs63 : stack < 2 ^ 63) {σ : State} (hK : KG p stack σ) :
    WP isa (Impl.SlhDsa.X86_64.Shake.keyGen p f) σ fun s' => abiPreserved σ s' ∧ (kgK p stack).post σ s' := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have hhp : 2 ≤ p.hp := by rcases hh with h | h | h | h <;> omega
  have hhp9 : p.hp ≤ 9 := by rcases hh with h | h | h | h <;> omega
  have hL := sigLen_le hz hh
  have eT : Layout.oSigTmp = 31648 := rfl
  have e2 : oKgSave = 34080 := rfl
  have eK : Layout.oKeys = 3168 := rfl
  have eA : Layout.oA = 3296 := rfl
  obtain ⟨S, hS⟩ : ∃ S, σ.gpr .rcx = S := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, σ.gpr .rdi = X := ⟨_, rfl⟩
  have hw : (⟨S, 2 ^ 16⟩ : Region) ∈ σ.wr := by rw [hK.wr, hS]; simp [scratchLen]
  have hr : (⟨X, 3 * p.n⟩ : Region) ∈ σ.rd := by rw [hK.rd, hX]; simp
  have hdis : Region.Disjoint ⟨X, 3 * p.n⟩ ⟨S, 2 ^ 16⟩ := by rw [← hX, ← hS]; exact hK.d_seed_scr
  have dS : (below (σ.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩ := by rw [← hS]; exact hK.stk_scr
  unfold Impl.SlhDsa.X86_64.Shake.keyGen
  refine WP.seq (WP.mono_mx (pro_nm p) (pro_ok hn32 hn8 hd hS hX hw hr (by rw [← hX]; exact hK.f_seed) hdis)
    fun u hu hmu => ?_)
  obtain ⟨hpre, hc, hw'⟩ := call_pre hz hh (by omega) hs63 hK hS hu
  have hcode : Impl.SlhDsa.X86_64.Shake.xmssCode p f =
      Impl.SlhDsa.X86_64.Xmss.xmssTree (Wots4.L p) p.hp f.t4name f.wotsName f.levelsName T.code := by
    rw [Impl.SlhDsa.X86_64.Shake.xmssCode, ht]; rfl
  rw [hcode]
  refine WP.seq (XmssTree.xmsscall_ok hz T f.t4name f.wotsName f.levelsName f.xmssName (stack := stack - 8)
    (by omega) (by omega) hhp hhp9 hpre hc hw' fun s' hrd hwr hcs hfr ⟨s₂, hm₂, _, hpost⟩ hmx => ?_)
  -- the call's entry
  generalize hv : u.callEntry.withRegions [] (callW p S) = v at hpost
  have hvdi : v.gpr .rdi = S := by rw [← hv, State.withRegions_gpr, State.callEntry_gpr _ (by decide), hu.rdi]
  have hvdx : v.gpr .rdx = at' S Layout.oSigTmp := by
    rw [← hv, State.withRegions_gpr, State.callEntry_gpr _ (by decide), hu.rdx]
  have hvsp : v.gpr .rsp = σ.gpr .rsp - 8 := by rw [← hv, State.withRegions_gpr, State.callEntry_rsp, hu.sp]
  have h8 : (below (u.gpr .rsp) 8).Disjoint ⟨S, 2 ^ 16⟩ := by
    rw [hu.sp]; exact dS.sub_left (below_sub (by omega) (by omega))
  have hvb : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 → bytesAt v.mem (at' S o) l = bytesAt u.mem (at' S o) l := fun {o l} h => by
    rw [← hv, State.withRegions_mem]
    exact bytesAt_frame (XmssTree.frame_callEntry u) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h8.sub_right (Levels.sub_scr S h)).symm) (by omega)
  have hvw : ∀ {o : Nat}, o + 8 ≤ 2 ^ 16 → v.mem.readW (at' S o) 64 = u.mem.readW (at' S o) 64 := fun {o} h => by
    rw [← hv, State.withRegions_mem]
    exact Thash4Avx.readW_frame (XmssTree.frame_callEntry u) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h8.sub_right (Levels.sub_scr S h)).symm
  have henv : Env p v.mem S (bytesAt σ.mem (X + BitVec.ofNat 64 (p.n * 2)) p.n) (Proof.SlhDsa.layerTree (p.d - 1) 0) := by
    rw [← hv, State.withRegions_mem]
    exact Env.of_frame hn32 hu.env ((XmssTree.frame_callEntry u).mono fun r hr => List.mem_append_right _ hr) h8
  dsimp only [xmssContract] at hpost
  rw [hvdi] at hpost
  obtain ⟨-, hroot, -, hF⟩ := hpost _ _ _ henv rfl
  rw [hvdx, hvsp, hm₂] at hF
  rw [hm₂] at hroot
  -- what the call keeps
  have hkd : ∀ {o l : Nat}, ((Layout.oKeys ≤ o ∧ o + l ≤ Layout.oA) ∨ (oKgSave ≤ o ∧ o + l ≤ 2 ^ 16)) →
      ∀ r ∈ changes p S ++ [⟨at' S Layout.oSigTmp, p.xmssSigLen⟩, below (σ.gpr .rsp - 8) (stack - 8)],
        Region.Disjoint ⟨at' S o, l⟩ r := fun {o l} ho r hr => by
    have hb : o + l ≤ 2 ^ 16 := by rcases ho with h | h <;> omega
    rcases List.mem_append.mp hr with hr | hr
    · rcases ho with h | h
      · exact keys_disj hn32 S h.1 h.2 r hr
      · exact (Offset.disjoint_base S (d := o) (k := Layout.oSigTmp) (by omega) (by omega)).sub_right
          (Levels.changes_low hn32 S r hr)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rcases ho with h | h
        · exact disj_scr S (by omega) (by omega) (by omega)
        · exact disj_scr S (by omega) (by omega) (by omega)
      · exact ((dS.sub_left (fun x hx => below_sub (sp := σ.gpr .rsp) (a := stack - 8 + 8) (by omega) (by omega) x
          (below_callee _ _ x hx))).sub_right (Levels.sub_scr S hb)).symm
  have hkeys : ∀ c < 3, bytesAt s'.mem (at' S (Layout.oKeys + 32 * c)) p.n =
      bytesAt σ.mem (X + BitVec.ofNat 64 (p.n * c)) p.n := fun c hc => by
    rw [bytesAt_frame hF (hkd (.inl ⟨by omega, by omega⟩)) (by omega), hvb (by omega)]
    exact hu.keys c hc
  have hsv : ∀ i < 6, s'.mem.readW (at' S (oKgSave + 8 * i)) 64 = σ.gpr (savedRegs.getD i .rbx) := fun i hi => by
    rw [Thash4Avx.readW_frame hF (hkd (.inr ⟨by omega, by omega⟩)), hvw (by omega)]
    exact hu.saved i hi
  have hcs' : ∀ r ∈ calleeSaved, s'.gpr r = u.gpr r := hcs
  have hb' : s'.gpr .rbx = S := by rw [hcs' _ (by decide), hu.bx]
  have h12 : s'.gpr .r12 = σ.gpr .rsi := by rw [hcs' _ (by decide), hu.r12]
  have h13 : s'.gpr .r13 = σ.gpr .rdx := by rw [hcs' _ (by decide), hu.r13]
  have hsp' : s'.gpr .rsp = σ.gpr .rsp := by rw [hcs' _ (by decide), hu.sp]
  have hwS : (⟨S, 2 ^ 16⟩ : Region) ∈ s'.wr := by rw [hwr, hu.wr]; exact hw
  have hsk : (⟨σ.gpr .rsi, 4 * p.n⟩ : Region) ∈ s'.wr := by rw [hwr, hu.wr, hK.wr]; simp [Params.skLen]
  have hpk : (⟨σ.gpr .rdx, 2 * p.n⟩ : Region) ∈ s'.wr := by rw [hwr, hu.wr, hK.wr]; simp [Params.pkLen]
  have dsk : Region.Disjoint ⟨σ.gpr .rsi, 4 * p.n⟩ ⟨S, 2 ^ 16⟩ := by rw [← hS]; exact hK.d_sk_scr
  have dpk : Region.Disjoint ⟨σ.gpr .rdx, 2 * p.n⟩ ⟨S, 2 ^ 16⟩ := by rw [← hS]; exact hK.d_pk_scr
  have hsk0 : bytesAt v.mem (at' S Layout.oSkSeed) p.n = bytesAt σ.mem (X + BitVec.ofNat 64 (p.n * 0)) p.n := by
    rw [hvb (by rw [show Layout.oSkSeed = 3168 from rfl]; omega)]; exact hu.keys 0 (by decide)
  refine WP.mono_mx (tail_nm p) (Q := fun t => t.mxcsr = s'.mxcsr → abiPreserved σ t ∧ (kgK p stack).post σ t)
    (tail_ok hn32 hn8 hb' h12 h13 hwS hsk hpk hK.f_sk hK.f_pk dsk dpk hK.d_sk_pk hsv hsp'
      fun t trd twr tcs tsk tpk tfr => fun hmt => ?_) fun _ h hm => h hm
  refine ⟨⟨tcs, ?_, by rw [hmt, hmx, hmu]⟩, ?_⟩
  · -- the return address
    have hd8 : 8 * (T.code.depth + 3) ≤ 32 := by have := T.depth_le; omega
    have dsc : Region.Disjoint (retR σ) ⟨S, 2 ^ 16⟩ := by rw [← hS]; exact hK.ret_scr
    have hsub : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 → Region.Disjoint (retR σ) ⟨at' S o, l⟩ :=
      fun h => dsc.sub_right (Levels.sub_scr S h)
    rw [Thash4Avx.readW_frame tfr fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hsub (by rw [show Layout.oPkRoot = 3264 from rfl]; omega)
        · exact hK.ret_sk
        · exact hK.ret_pk,
      Thash4Avx.readW_frame hfr fun r hr => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with (rfl | rfl) | rfl
        · exact dsc
        · exact hsub (by omega)
        · rw [hu.sp]; exact Offset.base_disjoint_below _ (by omega),
      Thash4Avx.readW_frame hu.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dsc]
  · show (bytesAt t.mem (σ.gpr .rsi) (4 * p.n), bytesAt t.mem (σ.gpr .rdx) (2 * p.n)) = kgOut p σ
    have k0 := hkeys 0 (by decide)
    have k1 := hkeys 1 (by decide)
    have k2 := hkeys 2 (by decide)
    rw [show Layout.oKeys + 32 * 0 = Layout.oKeys from rfl] at k0
    rw [show Layout.oKeys + 32 * 1 = Layout.oKeys + 32 from rfl] at k1
    rw [show Layout.oKeys + 32 * 2 = Layout.oKeys + 64 from rfl] at k2
    rw [tsk, tpk, k0, k1, k2, hroot, hsk0, root_adrs]
    simp only [kgOut, hX, keyGenInternal]
    rw [chunk_bytesAt _ _ (c := 3) (by decide), chunk_bytesAt _ _ (c := 3) (by decide),
      chunk_bytesAt _ _ (c := 3) (by decide)]

end VG.Proof.SlhDsa.X86_64.KeyGen
