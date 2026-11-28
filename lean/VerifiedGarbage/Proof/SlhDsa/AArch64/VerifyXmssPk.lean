module

-- separate module: the WOTS+ public key and the path, which the proof of the whole function does not change

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyXmssChains
import VerifiedGarbage.Proof.SlhDsa.AArch64.TopLanes
import VerifiedGarbage.Proof.SlhDsa.AArch64.TopIdx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64, `xmssPk`: the WOTS⁺ public key and the path

`wotsPk_ok`: the fields of lane 0 of `B`'s address (type `WOTS_PK`), `T_len`
of the chains' ends there, copied to lane 0 of `A`'s message; `path_ok`: the
`h′` heights of the authentication path in lane 0 of `A`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.XmssPk

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.SlhDsa (adrsOf)
open VG.Proof.SlhDsa.AArch64.TreeBase (Up in_scr in_scr' wp_subr wp_lsr wp_movz wp_mov wp_addi wp_subi wp_addr wp_and)

variable {p : Params}

/-- A write of 4 bytes at `a` keeps the 4 bytes at `b`, apart from it. -/
theorem keep4 {m m' : Mem} {S : Addr} {a b : Nat} (hf : Frame [⟨at' S a, 4⟩] m m') (h : a + 4 ≤ b ∨ b + 4 ≤ a)
    (ha : a + 4 ≤ 65536) (hb : b + 4 ≤ 65536) : bytesAt m' (at' S b) 4 = bytesAt m (at' S b) 4 :=
  TreeBase.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint S (by omega) (by omega) (by omega)) (by decide)

/-- The fields lane 0 of `B`'s address. -/
def bW (p : Params) (S : Addr) : List Region :=
  [⟨at' S (Layout.laneB 0 + p.n + 16), 4⟩, ⟨at' S (Layout.laneB 0 + p.n + 20), 4⟩,
    ⟨at' S (Layout.laneB 0 + p.n + 24), 4⟩, ⟨at' S (Layout.laneB 0 + p.n + 28), 4⟩]

theorem bW_safe (hz : Sz p) {S : Addr} : ∀ r ∈ bW p S, ∃ o l, r = ⟨at' S o, l⟩ ∧ Safe p o l := by
  have hn32 := hz.n32
  intro r hr
  simp only [bW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  all_goals exact ⟨_, _, rfl, .inr (.inr ⟨0, by decide, .inr ⟨by omega, by simp only [Layout.strideB]; omega⟩⟩)⟩

/-- The fields of lane 0 of `B`'s address: type `WOTS_PK`, key pair `x20`. -/
theorem fieldsB_ok (hz : Sz p) {t : State} {S : Addr} (h19 : t.gpr .x19 = S) (hw : (⟨S, 65536⟩ : Region) ∈ t.wr)
    (h20 : (t.gpr .x20).toNat < 2 ^ 32) {is : List Instr} {Q : State → Prop}
    (K : ∀ t', Keep [.x9] t t' → Frame (bW p S) t.mem t'.mem →
      bytesAt t'.mem (at' S (Layout.laneB 0 + p.n + 16)) 16 =
        toByte 1 4 ++ toByte (t.gpr .x20).toNat 4 ++ toByte 0 4 ++ toByte 0 4 → WP isa (.block is) t' Q) :
    WP isa (.block (Impl.SlhDsa.AArch64.setField .x19 (Layout.laneB 0 + p.n + 16) 1 ++
      Impl.SlhDsa.AArch64.setFieldR .x19 (Layout.laneB 0 + p.n + 20) .x20 ++
      Impl.SlhDsa.AArch64.setField .x19 (Layout.laneB 0 + p.n + 24) 0 ++
      Impl.SlhDsa.AArch64.setField .x19 (Layout.laneB 0 + p.n + 28) 0 ++ is)) t Q := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have eB : Layout.laneB 0 = 3648 := rfl
  simp only [List.append_assoc]
  refine setField_ok (b := .x19) (by decide) ⟨by rw [eB]; omega, by rw [eB]; omega⟩
    (by rw [h19]; exact in_scr hw (by rw [eB]; omega)) fun t₁ P₁ => ?_
  have g₁ : t₁.gpr .x19 = S := by rw [P₁.keep.get .x19, h19]
  have x20₁ : t₁.gpr .x20 = t.gpr .x20 := P₁.keep.get .x20
  refine setFieldR_ok (b := .x19) (r := .x20) (by decide) (by rw [x20₁]; exact h20)
    ⟨by rw [eB]; omega, by rw [eB]; omega⟩ (by rw [g₁, P₁.keep.wr]; exact in_scr hw (by rw [eB]; omega))
    fun t₂ P₂ => ?_
  have g₂ : t₂.gpr .x19 = S := by rw [P₂.keep.get .x19, g₁]
  refine setField_ok (b := .x19) (by decide) ⟨by rw [eB]; omega, by rw [eB]; omega⟩
    (by rw [g₂, P₂.keep.wr, P₁.keep.wr]; exact in_scr hw (by rw [eB]; omega)) fun t₃ P₃ => ?_
  have g₃ : t₃.gpr .x19 = S := by rw [P₃.keep.get .x19, g₂]
  refine setField_ok (b := .x19) (by decide) ⟨by rw [eB]; omega, by rw [eB]; omega⟩
    (by rw [g₃, P₃.keep.wr, P₂.keep.wr, P₁.keep.wr]; exact in_scr hw (by rw [eB]; omega)) fun t₄ P₄ => ?_
  have b₁ := P₁.bytes; have f₁ := P₁.frame
  have b₂ := P₂.bytes; have f₂ := P₂.frame
  have b₃ := P₃.bytes; have f₃ := P₃.frame
  have b₄ := P₄.bytes; have f₄ := P₄.frame
  rw [h19] at b₁ f₁
  rw [g₁, x20₁] at b₂
  rw [g₁] at f₂
  rw [g₂] at b₃ f₃
  rw [g₃] at b₄ f₄
  refine K t₄ (((P₁.keep.trans P₂.keep).trans (P₃.keep.trans P₄.keep)).mono (by simp))
    (((f₁.mono (by simp [bW])).trans (f₂.mono (by simp [bW]))).trans ((f₃.mono (by simp [bW])).trans
      (f₄.mono (by simp [bW])))) ?_
  rw [show (16 : Nat) = 4 + (4 + (4 + 4)) from rfl]
  simp only [bytesAt_add, addr_add]
  rw [show Layout.laneB 0 + p.n + 16 + 4 = Layout.laneB 0 + p.n + 20 by omega,
    show Layout.laneB 0 + p.n + 16 + 4 + 4 = Layout.laneB 0 + p.n + 24 by omega,
    show Layout.laneB 0 + p.n + 16 + 4 + 4 + 4 = Layout.laneB 0 + p.n + 28 by omega]
  have bd : ∀ c, c < 4 → Layout.laneB 0 + p.n + 16 + 4 * c + 4 ≤ 65536 := fun c hc => by rw [eB]; omega
  rw [keep4 (S := S) f₄ (by omega) (by rw [eB]; omega) (by rw [eB]; omega),
    keep4 (S := S) f₃ (by omega) (by rw [eB]; omega) (by rw [eB]; omega),
    keep4 (S := S) f₂ (by omega) (by rw [eB]; omega) (by rw [eB]; omega), b₁,
    keep4 (S := S) f₄ (by omega) (by rw [eB]; omega) (by rw [eB]; omega),
    keep4 (S := S) f₃ (by omega) (by rw [eB]; omega) (by rw [eB]; omega), b₂,
    keep4 (S := S) f₄ (by omega) (by rw [eB]; omega) (by rw [eB]; omega), b₃, b₄]
  simp only [List.append_assoc]

/-- `thashCall` on the lanes `B`, with messages of `n + 32 + len·n` bytes. -/
theorem thB_ok (hz : Sz p) (T : Thash4Impl p.n) (name : String) {t : State} {S : Addr}
    (h19 : t.gpr .x19 = S) (hw : (⟨S, 65536⟩ : Region) ∈ t.wr) (hfit : S.toNat + 65536 ≤ 2 ^ 64)
    {len : Nat} (hl : len = p.n + 32 + p.len * p.n) {Q : State → Prop}
    (K : ∀ t', t'.rd = t.rd → t'.wr = t.wr → t'.sp = t.sp → (∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) →
      (∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) →
      (∀ k < 4, bytesAt t'.mem (at' S (Layout.laneB k + p.n + 32)) p.n =
        shake256 (bytesAt t.mem (at' S (Layout.laneB k)) len) p.n) →
      Frame (Wots4.t4ch p.n S Layout.oB Layout.strideB) t.mem t'.mem → Q t') :
    WP isa (Impl.SlhDsa.AArch64.thashCall ⟨p.n, p.len⟩ name T.code Layout.oB Layout.strideB len) t Q := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have hn16 := hz.n16
  have hL := hz.len
  have hln : p.len * p.n = 2 * p.n * p.n + 3 * p.n := by rw [hL, Nat.add_mul]
  have hnn : 2 * p.n * p.n + 3 * p.n ≤ 2 * 32 * 32 + 3 * 32 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn32) hn32; omega
  have hm8 : p.len * p.n % 8 = 0 := by rw [Nat.mul_mod, hn8, Nat.mul_zero, Nat.zero_mod]
  have hlen : len ≤ 2208 := by omega
  refine WP.seq (WP.mono (Q := fun (u : State) => u.gpr .x0 = at' S Layout.oB ∧ u.gpr .x1 = BitVec.ofNat 64 Layout.strideB ∧
      u.gpr .x2 = BitVec.ofNat 64 len ∧ u.gpr .x3 = at' S (Layout.oB + p.n + 32) ∧ u.gpr .x4 = S ∧
      Only [.x0, .x1, .x2, .x3, .x4] t u) ?_ ?_)
  · simp only [Impl.SlhDsa.AArch64.thashArgs, Impl.SlhDsa.AArch64.lea, show Layout.oB < 4096 by decide, ↓reduceIte,
      List.cons_append, List.nil_append]
    refine MlKem.AArch64.wp_addImm (by decide) fun u₁ o₁ e₁ => MlKem.AArch64.wp_movz fun u₂ o₂ e₂ =>
      MlKem.AArch64.wp_movz fun u₃ o₃ e₃ => MlKem.AArch64.wp_addImm (by simp only [Impl.SlhDsa.AArch64.Layout.msgOff]; omega)
      fun u₄ o₄ e₄ => MlKem.AArch64.wp_addImm (by decide) fun u₅ o₅ e₅ => MlKem.AArch64.wp_nil ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).mono (by simp)⟩
    · rw [o₅.get .x0, o₄.get .x0, o₃.get .x0, o₂.get .x0, e₁, h19]
    · rw [o₅.get .x1, o₄.get .x1, o₃.get .x1, e₂, imm16 (by decide)]
    · rw [o₅.get .x2, o₄.get .x2, e₃, imm16 (by omega)]
    · rw [o₅.get .x3, e₄, o₃.get .x0, o₂.get .x0, e₁, h19, addr_add]; rfl
    · rw [e₅, BitVec.add_zero, o₄.get .x19, o₃.get .x19, o₂.get .x19, o₁.get .x19, h19]
  · intro u ⟨u0, u1, u2, u3, u4, ou⟩
    refine Wots4.t4call_ok T name (S := S) (o := Layout.oB) (st := Layout.strideB) (len := len)
      (by rw [ou.wr]; exact hw) hfit (by decide) (by decide) u0 u1 u2 u3 u4 (by omega)
      (by omega) (by simp only [Layout.strideB]; omega)
      (by simp only [Layout.strideB]; omega) fun t' r' w' sp' g' v' b' f' => K t' (by rw [r', ou.rd])
      (by rw [w', ou.wr]) (by rw [sp', ou.sp]) (fun r hr h30 => by
        rw [g' r hr h30, ou.gpr r (by revert r; decide)]) (fun r hr => by rw [v' r hr, ou.vcs r hr])
      (fun k hk => ?_) (by rw [ou.mem] at f'; exact f')
    have := b' k hk
    rw [ou.mem, show Layout.oB + k * Layout.strideB = Layout.laneB k by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega] at this
    exact this

theorem t4chB_safe (hz : Sz p) {S : Addr} :
    ∀ r ∈ Wots4.t4ch p.n S Layout.oB Layout.strideB, ∃ o l, r = ⟨at' S o, l⟩ ∧ Safe p o l := by
  have hn32 := hz.n32
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
    have hk' := List.mem_range.mp hk
    exact ⟨_, _, rfl, .inr (.inr ⟨k, hk', .inr ⟨by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega,
      by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega⟩⟩)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨0, workUsed, by simp [at'], .inl (by omega)⟩

theorem flatMap_range_congr {f g : Nat → List Byte} : ∀ {K : Nat}, (∀ i < K, f i = g i) →
    (List.range K).flatMap f = (List.range K).flatMap g
  | 0, _ => rfl
  | K + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, flatMap_range_congr fun i hi => h i (by omega),
      List.flatMap_singleton, List.flatMap_singleton, h K (by omega)]

theorem bytesAt_flat (m : Mem) (b : Addr) (n : Nat) : ∀ k, bytesAt m b (k * n) =
    (List.range k).flatMap fun c => bytesAt m (b + BitVec.ofNat 64 (c * n)) n
  | 0 => by simp [bytesAt]
  | k + 1 => by
    rw [Nat.succ_mul, bytesAt_add, bytesAt_flat m b n k, List.range_succ, List.flatMap_append,
      List.flatMap_singleton]

/-- The WOTS⁺ public key, from the chains' ends, in lane 0 of `A`'s message. -/
theorem wotsPk_ok (hz : Sz p) (T : Thash4Impl p.n) {f : Impl.SlhDsa.AArch64.Shake.Fns} (ht : f.t4 = T.code)
    {σ t : State} {S sig : Addr} {pk a : List Byte} {D : List Nat}
    (hR : Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32)
    (hx : XK p σ S sig pk a D t)
    (hE : ∀ c < p.len, bytesAt t.mem (at' S (endAt p c)) p.n = chainEnd p σ sig pk a D c) :
    WP isa (Impl.SlhDsa.AArch64.Verify.wotsPk p f) t fun t' => XK p σ S sig pk a D t' ∧
      bytesAt t'.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n =
        shake256 (pk ++ adrsOf a 1 (σ.gpr .x1).toNat 0 0 ++
          (List.range p.len).flatMap (chainEnd p σ sig pk a D)) p.n := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have hL := hz.len
  have eB : Layout.laneB 0 = 3648 := rfl
  have eA : Layout.laneA 0 = 3136 := rfl
  have hfit : S.toNat + 65536 ≤ 2 ^ 64 := by have := hR.scr_fit; simpa [scratchLen] using this
  have hwS : (⟨S, 65536⟩ : Region) ∈ t.wr := by rw [hx.wr]; exact TreeBase.regions_scr hR
  have hln : p.len * p.n = 2 * p.n * p.n + 3 * p.n := by rw [hL, Nat.add_mul]
  have hnn : 2 * p.n * p.n + 3 * p.n ≤ 2 * 32 * 32 + 3 * 32 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn32) hn32; omega
  have h8n : 8 * (p.n / 8) = p.n := by omega
  unfold Impl.SlhDsa.AArch64.Verify.wotsPk
  refine WP.seq ?_
  rw [← List.append_nil (Impl.SlhDsa.AArch64.setField .x19 (Layout.laneB 0 + _ + 28) 0)]
  refine fieldsB_ok hz hx.x19 hwS (by rw [hx.x20]; exact hidx) fun t₁ k₁ f₁ b₁ => MlKem.AArch64.wp_nil ?_
  have X₁ : XK p σ S sig pk a D t₁ := XK.step hz hx (by decide) k₁ f₁ (bW_safe hz)
  rw [hx.x20] at b₁
  have hE₁ : bytesAt t₁.mem (at' S (Layout.laneB 0 + p.n + 32)) (p.len * p.n) =
      (List.range p.len).flatMap (chainEnd p σ sig pk a D) := by
    rw [TreeBase.bytesAt_frame f₁ (fun r hr => by
      simp only [bW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      all_goals exact Offset.disjoint S (by omega) (by rw [eB]; omega) (by rw [eB]; omega)) (by omega),
      bytesAt_flat]
    refine flatMap_range_congr fun c hc => ?_
    rw [addr_add, ← hE c hc]
  rw [ht]
  refine WP.seq (thB_ok hz T f.t4name X₁.x19 (by rw [X₁.wr]; exact TreeBase.regions_scr hR) hfit rfl
    fun t₂ r₂ w₂ sp₂ g₂ v₂ b₂ fr₂ => ?_)
  have X₂ : XK p σ S sig pk a D t₂ := XK.call hz X₁ r₂ w₂ sp₂ g₂ v₂ fr₂ (t4chB_safe hz)
  rw [← List.append_nil (Impl.SlhDsa.AArch64.copyWords _ _ _ _ _)]
  have hw₂ : (⟨S, 65536⟩ : Region) ∈ t₂.wr := by rw [X₂.wr]; exact TreeBase.regions_scr hR
  refine copyWords_ok (t := .x19) (sr := .x19) (d₂ := Layout.laneA 0 + (p.n + 32)) (d₁ := Layout.laneB 0 + (p.n + 32))
    (w := p.n / 8) ⟨by decide, by decide, ⟨by rw [eB]; omega, by rw [eB]; omega⟩, ⟨by rw [eA]; omega, by rw [eA]; omega⟩,
      (by rw [X₂.x19, h8n]; exact in_scr' hw₂ (by rw [eB]; omega)),
      (by rw [X₂.x19, h8n]; exact in_scr hw₂ (by rw [eA]; omega)),
      (by rw [X₂.x19, h8n]; exact Offset.disjoint S (by rw [eA, eB]; omega) (by rw [eA]; omega) (by rw [eB]; omega))⟩
    fun t₃ k₃ f₃ b₃ => MlKem.AArch64.wp_nil ⟨XK.step hz X₂ (by decide) k₃ f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, _, by rw [X₂.x19], .inr (.inr ⟨0, by decide, .inl ⟨by omega, by
        simp only [Layout.strideA]; omega⟩⟩)⟩), ?_⟩
  rw [X₂.x19, h8n, show Layout.laneA 0 + (p.n + 32) = Layout.laneA 0 + p.n + 32 by omega,
    show Layout.laneB 0 + (p.n + 32) = Layout.laneB 0 + p.n + 32 by omega] at b₃
  rw [b₃, b₂ 0 (by decide)]
  refine congrArg (fun x => shake256 x p.n) ?_
  rw [show p.n + 32 + p.len * p.n = p.n + (16 + (16 + p.len * p.n)) by omega]
  simp only [bytesAt_add, addr_add]
  rw [X₁.env.seedB 0 (by decide), X₁.env.adrsB 0 (by decide), show Layout.laneB 0 + p.n + 16 = Layout.laneB 0 + p.n + 16 from rfl,
    b₁, show Layout.laneB 0 + p.n + 16 + 16 = Layout.laneB 0 + p.n + 32 by omega, hE₁]
  simp only [adrsOf, List.append_assoc]

/-! ## The path -/

theorem and1 (v : Nat) (hv : v < 2 ^ 64) :
    (BitVec.ofNat 64 v &&& (1 : BitVec 16).setWidth 64) = BitVec.ofNat 64 (v % 2) := by
  rw [show (1 : BitVec 16).setWidth 64 = BitVec.ofNat 64 (2 ^ 1 - 1) by decide]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt (show 2 ^ 1 - 1 < 2 ^ 64 by decide), Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem shr1 (v : Nat) (hv : v < 2 ^ 64) : BitVec.ofNat 64 v >>> 1 = BitVec.ofNat 64 (v / 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt (by omega)]

theorem bit_eq (q : Nat) : (BitVec.ofNat 64 (q % 2) == 0) = decide (q % 2 = 0) := by
  rcases Nat.mod_two_eq_zero_or_one q with h | h <;> rw [h] <;> decide

theorem H_shake' (hz : Sz p) (pk : List Byte) (ad : Adrs) (M : List Byte) : H p pk ad M = shake256 (pk ++ ad ++ M) p.n := by
  simp only [H, hz.shake, shakeAdrs]

/-- Node `z` of the authentication path. -/
theorem chunk_auth (m : Mem) (sig : Addr) {z : Nat} (h : p.len * p.n + p.n * z + p.n ≤ p.xmssSigLen) :
    chunk ((bytesAt m sig p.xmssSigLen).drop (p.len * p.n)) p.n z =
      bytesAt m (sig + BitVec.ofNat 64 (p.len * p.n + p.n * z)) p.n := by
  simp only [chunk, List.drop_drop]
  exact bytesAt_drop_take m sig (by omega)

/-- The fields lane 0 of `A`'s address. -/
def aF (p : Params) (S : Addr) : List Region :=
  [⟨at' S (Layout.laneA 0 + p.n + 16), 4⟩, ⟨at' S (Layout.laneA 0 + p.n + 20), 4⟩,
    ⟨at' S (Layout.laneA 0 + p.n + 24), 4⟩, ⟨at' S (Layout.laneA 0 + p.n + 28), 4⟩]

theorem aF_safe (hz : Sz p) {S : Addr} : ∀ r ∈ aF p S, ∃ o l, r = ⟨at' S o, l⟩ ∧ Safe p o l := by
  have hn32 := hz.n32
  intro r hr
  simp only [aF, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  all_goals exact ⟨_, _, rfl, .inr (.inr ⟨0, by decide, .inl ⟨by omega, by simp only [Layout.strideA]; omega⟩⟩)⟩

/-- The fields of lane 0 of `A`'s address for height `z + 1` (type `TREE`,
index `x26 / 2`). -/
theorem fieldsA_ok (hz : Sz p) {t : State} {S : Addr} (h19 : t.gpr .x19 = S) (hw : (⟨S, 65536⟩ : Region) ∈ t.wr)
    {z q : Nat} (h25 : t.gpr .x25 = BitVec.ofNat 64 z) (hz32 : z + 1 < 2 ^ 32) (h26 : t.gpr .x26 = BitVec.ofNat 64 q)
    (hq : q < 2 ^ 32) {is : List Instr} {Q : State → Prop}
    (K : ∀ t', Keep [.x9, .x10, .x26] t t' → Frame (aF p S) t.mem t'.mem → t'.gpr .x26 = BitVec.ofNat 64 (q / 2) →
      bytesAt t'.mem (at' S (Layout.laneA 0 + p.n + 16)) 16 =
        toByte 2 4 ++ toByte 0 4 ++ toByte (z + 1) 4 ++ toByte (q / 2) 4 → WP isa (.block is) t' Q) :
    WP isa (.block (Impl.SlhDsa.AArch64.setField .x19 (Layout.laneA 0 + p.n + 16) 2 ++
      Impl.SlhDsa.AArch64.setField .x19 (Layout.laneA 0 + p.n + 20) 0 ++
      ([.addImm .x .x10 .x25 1] : List Instr) ++ Impl.SlhDsa.AArch64.setFieldR .x19 (Layout.laneA 0 + p.n + 24) .x10 ++
      ([.lsr .x .x26 .x26 1] : List Instr) ++ Impl.SlhDsa.AArch64.setFieldR .x19 (Layout.laneA 0 + p.n + 28) .x26 ++ is)) t Q := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have eA : Layout.laneA 0 = 3136 := rfl
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine setField_ok (b := .x19) (by decide) ⟨by rw [eA]; omega, by rw [eA]; omega⟩
    (by rw [h19]; exact in_scr hw (by rw [eA]; omega)) fun t₁ P₁ => ?_
  have g₁ : t₁.gpr .x19 = S := by rw [P₁.keep.get .x19, h19]
  refine setField_ok (b := .x19) (by decide) ⟨by rw [eA]; omega, by rw [eA]; omega⟩
    (by rw [g₁, P₁.keep.wr]; exact in_scr hw (by rw [eA]; omega)) fun t₂ P₂ => ?_
  have g₂ : t₂.gpr .x19 = S := by rw [P₂.keep.get .x19, g₁]
  refine wp_addi (by decide) fun t₃ u₃ => ?_
  have g₃ : t₃.gpr .x19 = S := by rw [u₃.other _ (by decide), g₂]
  have x10₃ : t₃.gpr .x10 = BitVec.ofNat 64 (z + 1) := by
    rw [u₃.gpr, P₂.keep.get .x25, P₁.keep.get .x25, h25, BitVec.ofNat_add]
  have hz1 : (t₃.gpr .x10).toNat = z + 1 := by rw [x10₃, BitVec.toNat_ofNat]; omega
  refine setFieldR_ok (b := .x19) (r := .x10) (by decide) (by rw [hz1]; exact hz32)
    ⟨by rw [eA]; omega, by rw [eA]; omega⟩ (by rw [g₃, u₃.wr, P₂.keep.wr, P₁.keep.wr]; exact in_scr hw (by rw [eA]; omega))
    fun t₄ P₄ => ?_
  refine wp_lsr (by decide) fun t₅ u₅ => ?_
  have g₅ : t₅.gpr .x19 = S := by rw [u₅.other _ (by decide), P₄.keep.get .x19, g₃]
  have x26₅ : t₅.gpr .x26 = BitVec.ofNat 64 (q / 2) := by
    rw [u₅.gpr, P₄.keep.get .x26, u₃.other _ (by decide), P₂.keep.get .x26, P₁.keep.get .x26, h26, shr1 q (by omega)]
  have hq2 : (t₅.gpr .x26).toNat = q / 2 := by rw [x26₅, BitVec.toNat_ofNat]; omega
  refine setFieldR_ok (b := .x19) (r := .x26) (by decide) (by rw [hq2]; omega)
    ⟨by rw [eA]; omega, by rw [eA]; omega⟩
    (by rw [g₅, u₅.wr, P₄.keep.wr, u₃.wr, P₂.keep.wr, P₁.keep.wr]; exact in_scr hw (by rw [eA]; omega))
    fun t₆ P₆ => ?_
  have b₁ := P₁.bytes; have f₁ := P₁.frame
  have b₂ := P₂.bytes; have f₂ := P₂.frame
  have b₄ := P₄.bytes; have f₄ := P₄.frame
  have b₆ := P₆.bytes; have f₆ := P₆.frame
  rw [h19] at b₁ f₁
  rw [g₁] at b₂ f₂
  rw [g₃, hz1] at b₄
  rw [g₃] at f₄
  rw [g₅, hq2] at b₆
  rw [g₅] at f₆
  rw [u₅.mem] at f₆
  rw [u₃.mem] at f₄
  refine K t₆ ((((P₁.keep.trans P₂.keep).trans ((upOnly u₃).keep.trans P₄.keep)).trans
      ((upOnly u₅).keep.trans P₆.keep)).mono (by simp))
    (((f₁.mono (by simp [aF])).trans (f₂.mono (by simp [aF]))).trans ((f₄.mono (by simp [aF])).trans
      (f₆.mono (by simp [aF])))) (by rw [P₆.keep.get .x26, x26₅]) ?_
  rw [show (16 : Nat) = 4 + (4 + (4 + 4)) from rfl]
  simp only [bytesAt_add, addr_add]
  rw [show Layout.laneA 0 + p.n + 16 + 4 = Layout.laneA 0 + p.n + 20 by omega,
    show Layout.laneA 0 + p.n + 16 + 4 + 4 = Layout.laneA 0 + p.n + 24 by omega,
    show Layout.laneA 0 + p.n + 16 + 4 + 4 + 4 = Layout.laneA 0 + p.n + 28 by omega]
  rw [keep4 (S := S) f₆ (by omega) (by rw [eA]; omega) (by rw [eA]; omega),
    keep4 (S := S) f₄ (by omega) (by rw [eA]; omega) (by rw [eA]; omega),
    keep4 (S := S) f₂ (by omega) (by rw [eA]; omega) (by rw [eA]; omega), b₁,
    keep4 (S := S) f₆ (by omega) (by rw [eA]; omega) (by rw [eA]; omega),
    keep4 (S := S) f₄ (by omega) (by rw [eA]; omega) (by rw [eA]; omega), b₂,
    keep4 (S := S) f₆ (by omega) (by rw [eA]; omega) (by rw [eA]; omega), b₄, b₆]
  simp only [List.append_assoc]

/-- The authentication path of the signature at `sig`. -/
abbrev auth (p : Params) (σ : State) (sig : Addr) : List Byte := (bytesAt σ.mem sig p.xmssSigLen).drop (p.len * p.n)

/-- Before height `z` of the path, from the WOTS⁺ public key `node0`. -/
structure PI (p : Params) (σ : State) (S sig : Addr) (pk a : List Byte) (D : List Nat) (node0 : List Byte) (z : Nat)
    (t : State) : Prop where
  xk : XK p σ S sig pk a D t
  x25 : t.gpr .x25 = BitVec.ofNat 64 z
  x26 : t.gpr .x26 = BitVec.ofNat 64 ((σ.gpr .x1).toNat / 2 ^ z)
  node : bytesAt t.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n =
    path p pk a 2 0 (σ.gpr .x1).toNat (auth p σ sig) z node0

/-- After the first block of height `z`: `x12` the path's node `z`, `x9` bit `z` of `idx`. -/
structure P1 (p : Params) (σ : State) (S sig : Addr) (pk a : List Byte) (D : List Nat) (node0 : List Byte) (z : Nat)
    (t : State) : Prop where
  xk : XK p σ S sig pk a D t
  x12 : t.gpr .x12 = sig + BitVec.ofNat 64 (p.len * p.n + p.n * z)
  x9 : t.gpr .x9 = BitVec.ofNat 64 ((σ.gpr .x1).toNat / 2 ^ z % 2)
  x25 : t.gpr .x25 = BitVec.ofNat 64 z
  x26 : t.gpr .x26 = BitVec.ofNat 64 ((σ.gpr .x1).toNat / 2 ^ z)
  node : bytesAt t.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n =
    path p pk a 2 0 (σ.gpr .x1).toNat (auth p σ sig) z node0

/-- After the branch of height `z`: the message of lane 0 of `A`. -/
structure P2 (p : Params) (σ : State) (S sig : Addr) (pk a : List Byte) (D : List Nat) (node0 : List Byte) (z : Nat)
    (u : State) : Prop where
  xk : XK p σ S sig pk a D u
  x25 : u.gpr .x25 = BitVec.ofNat 64 z
  x26 : u.gpr .x26 = BitVec.ofNat 64 ((σ.gpr .x1).toNat / 2 ^ z)
  msg : bytesAt u.mem (at' S (Layout.laneA 0 + p.n + 32)) (p.n + p.n) =
    (if (σ.gpr .x1).toNat / 2 ^ z % 2 = 0 then
      path p pk a 2 0 (σ.gpr .x1).toNat (auth p σ sig) z node0 ++ chunk (auth p σ sig) p.n z
    else chunk (auth p σ sig) p.n z ++ path p pk a 2 0 (σ.gpr .x1).toNat (auth p σ sig) z node0)

/-- The first block of height `z`. -/
theorem pathB1_ok (hz : Sz p)
    {σ : State} {S sig : Addr} {pk a : List Byte} {D : List Nat} {node0 : List Byte}
    (hR : Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32) {z : Nat}
    (hzh : z < p.hp) {t : State} (hI : PI p σ S sig pk a D node0 z t) :
    WP isa (.block ([Impl.SlhDsa.AArch64.Thash4.mov .x12 .x25] ++ Impl.SlhDsa.AArch64.mulN p.n .x12 .x13 ++
      ([.add .x .x12 .x12 .x21, .addImm .x .x12 .x12 (p.len * p.n), .movz .x .x9 1 0, .logic .and .x .x9 .x26 .x9] : List Instr))) t (P1 p σ S sig pk a D node0 z) := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have hL := hz.len
  have eA : Layout.laneA 0 = 3136 := rfl
  have h8n : 8 * (p.n / 8) = p.n := by omega
  have hfit : S.toNat + 65536 ≤ 2 ^ 64 := by have := hR.scr_fit; simpa [scratchLen] using this
  have hwS : (⟨S, 65536⟩ : Region) ∈ t.wr := by rw [hI.xk.wr]; exact TreeBase.regions_scr hR
  have hln : p.len * p.n = 2 * p.n * p.n + 3 * p.n := by rw [hL, Nat.add_mul]
  have hnn : 2 * p.n * p.n + 3 * p.n ≤ 2 * 32 * 32 + 3 * 32 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn32) hn32; omega
  have hzn : p.len * p.n + p.n * z + p.n ≤ p.xmssSigLen := by
    rw [xmssSigLen_eq', Nat.mul_comm p.n z]
    have := Nat.mul_le_mul_right p.n (show z + 1 ≤ p.hp by omega); rw [Nat.succ_mul] at this; omega
  have hLI := hI.xk.laneIn hR hidx
  have hz64 : p.len * p.n + p.n * z < 2 ^ 64 := by have := hLI.slen; have := hz.n16; omega
  obtain ⟨q, eq⟩ : ∃ q, (σ.gpr .x1).toNat / 2 ^ z = q := ⟨_, rfl⟩
  have hq : q < 2 ^ 32 := eq ▸ Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hidx
  have x26 := hI.x26
  rw [eq] at x26
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun t₁ u₁ => mulN_ok hz.nv (r := .x12) (tmp := .x13) (by decide) fun t₂ o₂ e₂ =>
    wp_addr fun t₃ u₃ => wp_addi (by omega) fun t₄ u₄ => wp_movz fun t₅ u₅ => wp_and fun t₆ u₆ =>
      MlKem.AArch64.wp_nil ?_
  have K6 : Keep [.x12, .x12, .x13, .x12, .x12, .x9, .x9] t t₆ :=
    (((((upOnly u₁).keep.trans o₂.keep).trans (upOnly u₃).keep).trans (upOnly u₄).keep).trans
      (upOnly u₅).keep).trans (upOnly u₆).keep
  have m6 : t₆.mem = t.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, o₂.mem, u₁.mem]
  have e12 : t₆.gpr .x12 = sig + BitVec.ofNat 64 (p.len * p.n + p.n * z) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, e₂, u₁.gpr, o₂.get .x21,
      u₁.other _ (by decide), hI.xk.x21, hI.x25, ← BitVec.ofNat_mul, BitVec.add_comm _ sig, BitVec.add_assoc,
      ← BitVec.ofNat_add, Nat.mul_comm z, Nat.add_comm (p.n * z)]
  have e9 : t₆.gpr .x9 = BitVec.ofNat 64 (q % 2) := by
    rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), o₂.get .x26,
      u₁.other _ (by decide), x26, and1 q (by omega)]
  have X₆ : XK p σ S sig pk a D t₆ := XK.step hz hI.xk (by decide) K6 (by rw [m6]; exact Frame.refl _ _)
    (fun r hr => absurd hr List.not_mem_nil)
  exact ⟨X₆, e12, by rw [e9, eq], by rw [K6.get .x25, hI.x25], by rw [K6.get .x26, x26, eq],
    by rw [m6, hI.node]⟩

/-- The branch of height `z`: the node and the path's node `z`, in the order bit `z` says. -/
theorem pathIte_ok (hz : Sz p)
    {σ : State} {S sig : Addr} {pk a : List Byte} {D : List Nat} {node0 : List Byte}
    (hR : Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32) {z : Nat}
    (hzh : z < p.hp) {t₆ : State} (hP : P1 p σ S sig pk a D node0 z t₆) :
    WP isa (.ite (.zero .x .x9)
      (.block (Impl.SlhDsa.AArch64.copyWords .x19 (Layout.laneA 0 + (p.n + 32) + p.n) .x12 0 (p.n / 8)))
      (.block (Impl.SlhDsa.AArch64.copyWords .x19 (Layout.laneA 0 + (p.n + 32) + p.n) .x19 (Layout.laneA 0 + (p.n + 32))
          (p.n / 8) ++ Impl.SlhDsa.AArch64.copyWords .x19 (Layout.laneA 0 + (p.n + 32)) .x12 0 (p.n / 8)))) t₆ (P2 p σ S sig pk a D node0 z) := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have hL := hz.len
  have eA : Layout.laneA 0 = 3136 := rfl
  have h8n : 8 * (p.n / 8) = p.n := by omega
  have hfit : S.toNat + 65536 ≤ 2 ^ 64 := by have := hR.scr_fit; simpa [scratchLen] using this
  have hln : p.len * p.n = 2 * p.n * p.n + 3 * p.n := by rw [hL, Nat.add_mul]
  have hnn : 2 * p.n * p.n + 3 * p.n ≤ 2 * 32 * 32 + 3 * 32 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn32) hn32; omega
  have hzn : p.len * p.n + p.n * z + p.n ≤ p.xmssSigLen := by
    rw [xmssSigLen_eq', Nat.mul_comm p.n z]
    have := Nat.mul_le_mul_right p.n (show z + 1 ≤ p.hp by omega); rw [Nat.succ_mul] at this; omega
  have hLI := hP.xk.laneIn hR hidx
  have hz64 : p.len * p.n + p.n * z < 2 ^ 64 := by have := hLI.slen; have := hz.n16; omega
  obtain ⟨q, eq⟩ : ∃ q, (σ.gpr .x1).toNat / 2 ^ z = q := ⟨_, rfl⟩
  have hq : q < 2 ^ 32 := eq ▸ Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hidx
  have e12 := hP.x12
  have e9 : t₆.gpr .x9 = BitVec.ofNat 64 (q % 2) := by rw [hP.x9, eq]
  have X₆ := hP.xk
  have hLI' := X₆.laneIn hR hidx
  have hw₆ : (⟨S, 65536⟩ : Region) ∈ t₆.wr := by rw [X₆.wr]; exact TreeBase.regions_scr hR
  have hsig₆ := X₆.laneIn hR hidx
  have dS : ∀ {o : Nat}, o + p.n ≤ 65536 →
      Region.Disjoint ⟨at' S o, p.n⟩ ⟨sig + BitVec.ofNat 64 (p.len * p.n + p.n * z), p.n⟩ := fun h =>
    (hLI'.dsig.symm.sub_left (Offset.sub_base S h)).sub_right (Offset.sub_base sig hzn)
  -- the message: the node and the path's node `z`, in the order bit `z` says
  obtain ⟨nd, end_⟩ : ∃ nd, path p pk a 2 0 (σ.gpr .x1).toNat (auth p σ sig) z node0 = nd := ⟨_, rfl⟩
  have hau : chunk (auth p σ sig) p.n z = bytesAt σ.mem (sig + BitVec.ofNat 64 (p.len * p.n + p.n * z)) p.n :=
    chunk_auth σ.mem sig hzn
  have hau₆ : bytesAt t₆.mem (sig + BitVec.ofNat 64 (p.len * p.n + p.n * z)) p.n = chunk (auth p σ sig) p.n z := by
    rw [X₆.sigB hz hR hzn, hau]
  have nd₆ : bytesAt t₆.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n = nd := by rw [hP.node, end_]
  have hmsg : 3168 + p.n + p.n + p.n ≤ 3264 := by omega
  refine WP.mono (Q := fun (u : State) => XK p σ S sig pk a D u ∧ u.gpr .x25 = BitVec.ofNat 64 z ∧
      u.gpr .x26 = BitVec.ofNat 64 q ∧ bytesAt u.mem (at' S (Layout.laneA 0 + p.n + 32)) (p.n + p.n) =
        (if q % 2 = 0 then nd ++ chunk (auth p σ sig) p.n z else chunk (auth p σ sig) p.n z ++ nd)) ?_
    fun u ⟨X, h25, h26, hm⟩ => ⟨X, h25, by rw [h26, eq], by rw [hm, eq, end_]⟩
  have k25 : t₆.gpr .x25 = BitVec.ofNat 64 z := hP.x25
  have k26 : t₆.gpr .x26 = BitVec.ofNat 64 q := by rw [hP.x26, eq]
  refine WP.ite _ (MlKem.AArch64.eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [e9, bit_eq] at hb
    have h0 : q % 2 = 0 := of_decide_eq_true hb
    rw [← List.append_nil (Impl.SlhDsa.AArch64.copyWords _ _ _ _ _)]
    refine copyWords_ok (t := .x19) (sr := .x12) (d₂ := Layout.laneA 0 + (p.n + 32) + p.n) (d₁ := 0) (w := p.n / 8)
      ⟨by decide, by decide, ⟨by decide, by omega⟩, ⟨by rw [eA]; omega, by rw [eA]; omega⟩,
        (by rw [e12, BitVec.add_zero, h8n]
            exact ⟨_, List.mem_append_left _ hsig₆.insig, Offset.contains_base sig hzn hz64⟩),
        (by rw [X₆.x19, h8n]; exact in_scr hw₆ (by rw [eA]; omega)),
        (by rw [X₆.x19, e12, BitVec.add_zero, h8n]; exact dS (by rw [eA]; omega))⟩
      fun t₇ k₇ f₇ b₇ => WP.block_nil ?_
    rw [X₆.x19, h8n] at f₇ b₇
    rw [e12, BitVec.add_zero, hau₆] at b₇
    refine ⟨XK.step hz X₆ (by decide) k₇ f₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, _, rfl, .inr (.inr ⟨0, by decide, .inl ⟨by omega, by simp only [Layout.strideA]; omega⟩⟩)⟩),
      by rw [k₇.get .x25, k25], by rw [k₇.get .x26, k26], ?_⟩
    simp only [h0, ↓reduceIte]
    rw [bytesAt_add, addr_add, show Layout.laneA 0 + p.n + 32 + p.n = Layout.laneA 0 + (p.n + 32) + p.n
      by omega, b₇, TreeBase.bytesAt_frame f₇ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint S (by omega) (by rw [eA]; omega) (by rw [eA]; omega)) (by omega), nd₆]
  · rw [e9, bit_eq] at hb
    have h1 : ¬ q % 2 = 0 := of_decide_eq_false hb
    refine copyWords_ok (t := .x19) (sr := .x19) (d₂ := Layout.laneA 0 + (p.n + 32) + p.n)
      (d₁ := Layout.laneA 0 + (p.n + 32)) (w := p.n / 8)
      ⟨by decide, by decide, ⟨by rw [eA]; omega, by rw [eA]; omega⟩, ⟨by rw [eA]; omega, by rw [eA]; omega⟩,
        (by rw [X₆.x19, h8n]; exact in_scr' hw₆ (by rw [eA]; omega)),
        (by rw [X₆.x19, h8n]; exact in_scr hw₆ (by rw [eA]; omega)),
        (by rw [X₆.x19, h8n]; exact Offset.disjoint S (by omega) (by rw [eA]; omega) (by rw [eA]; omega))⟩
      fun t₇ k₇ f₇ b₇ => ?_
    rw [X₆.x19, h8n] at f₇ b₇
    have X₇ : XK p σ S sig pk a D t₇ := XK.step hz X₆ (by decide) k₇ f₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, _, rfl, .inr (.inr ⟨0, by decide, .inl ⟨by omega, by simp only [Layout.strideA]; omega⟩⟩)⟩)
    have hw₇ : (⟨S, 65536⟩ : Region) ∈ t₇.wr := by rw [k₇.wr]; exact hw₆
    have e12₇ : t₇.gpr .x12 = sig + BitVec.ofNat 64 (p.len * p.n + p.n * z) := by rw [k₇.get .x12, e12]
    have hau₇ : bytesAt t₇.mem (sig + BitVec.ofNat 64 (p.len * p.n + p.n * z)) p.n = chunk (auth p σ sig) p.n z := by
      rw [X₇.sigB hz hR hzn, hau]
    rw [← List.append_nil (Impl.SlhDsa.AArch64.copyWords .x19 _ .x12 _ _)]
    refine copyWords_ok (t := .x19) (sr := .x12) (d₂ := Layout.laneA 0 + (p.n + 32)) (d₁ := 0) (w := p.n / 8)
      ⟨by decide, by decide, ⟨by decide, by omega⟩, ⟨by rw [eA]; omega, by rw [eA]; omega⟩,
        (by rw [e12₇, BitVec.add_zero, h8n, k₇.rd]
            exact ⟨_, List.mem_append_left _ hsig₆.insig, Offset.contains_base sig hzn hz64⟩),
        (by rw [X₇.x19, h8n]; exact in_scr hw₇ (by rw [eA]; omega)),
        (by rw [X₇.x19, e12₇, BitVec.add_zero, h8n]; exact dS (by rw [eA]; omega))⟩
      fun t₈ k₈ f₈ b₈ => WP.block_nil ?_
    rw [X₇.x19, h8n] at f₈ b₈
    rw [e12₇, BitVec.add_zero, hau₇] at b₈
    refine ⟨XK.step hz X₇ (by decide) k₈ f₈ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, _, rfl, .inr (.inr ⟨0, by decide, .inl ⟨by omega, by simp only [Layout.strideA]; omega⟩⟩)⟩),
      by rw [k₈.get .x25, k₇.get .x25, k25], by rw [k₈.get .x26, k₇.get .x26, k26], ?_⟩
    simp only [h1, ↓reduceIte]
    rw [bytesAt_add, addr_add, show Layout.laneA 0 + p.n + 32 + p.n = Layout.laneA 0 + (p.n + 32) + p.n
      by omega, show Layout.laneA 0 + p.n + 32 = Layout.laneA 0 + (p.n + 32) by omega, b₈,
      TreeBase.bytesAt_frame f₈ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint S (by omega) (by rw [eA]; omega) (by rw [eA]; omega)) (by omega), b₇,
      show Layout.laneA 0 + (p.n + 32) = Layout.laneA 0 + p.n + 32 by omega, nd₆]

/-- The address, the hash and the counter of height `z`. -/
theorem pathTail_ok (hz : Sz p) (T : Thash4Impl p.n) {f : Impl.SlhDsa.AArch64.Shake.Fns} (ht : f.t4 = T.code)
    {σ : State} {S sig : Addr} {pk a : List Byte} {D : List Nat} {node0 : List Byte}
    (hR : Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32) {z : Nat}
    (hzh : z < p.hp) (hh : p.hp < 4096) {u : State} (hP : P2 p σ S sig pk a D node0 z u) :
    WP isa (.seq (.block (Impl.SlhDsa.AArch64.setField .x19 (Layout.laneA 0 + p.n + 16) 2 ++
      Impl.SlhDsa.AArch64.setField .x19 (Layout.laneA 0 + p.n + 20) 0 ++
      ([.addImm .x .x10 .x25 1] : List Instr) ++ Impl.SlhDsa.AArch64.setFieldR .x19 (Layout.laneA 0 + p.n + 24) .x10 ++
      ([.lsr .x .x26 .x26 1] : List Instr) ++ Impl.SlhDsa.AArch64.setFieldR .x19 (Layout.laneA 0 + p.n + 28) .x26))
      (.seq (Impl.SlhDsa.AArch64.thashCall ⟨p.n, p.len⟩ f.t4name f.t4 Layout.oA Layout.strideA (3 * p.n + 32))
        (.block [.addImm .x .x25 .x25 1, .subImm .x .x9 .x25 p.hp]))) u fun t' =>
      PI p σ S sig pk a D node0 (z + 1) t' ∧ t'.gpr .x9 = BitVec.ofNat 64 (z + 1) - BitVec.ofNat 64 p.hp := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have hL := hz.len
  have eA : Layout.laneA 0 = 3136 := rfl
  have h8n : 8 * (p.n / 8) = p.n := by omega
  have hfit : S.toNat + 65536 ≤ 2 ^ 64 := by have := hR.scr_fit; simpa [scratchLen] using this
  have hln : p.len * p.n = 2 * p.n * p.n + 3 * p.n := by rw [hL, Nat.add_mul]
  have hnn : 2 * p.n * p.n + 3 * p.n ≤ 2 * 32 * 32 + 3 * 32 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn32) hn32; omega
  have hzn : p.len * p.n + p.n * z + p.n ≤ p.xmssSigLen := by
    rw [xmssSigLen_eq', Nat.mul_comm p.n z]
    have := Nat.mul_le_mul_right p.n (show z + 1 ≤ p.hp by omega); rw [Nat.succ_mul] at this; omega
  have hLI := hP.xk.laneIn hR hidx
  have hz64 : p.len * p.n + p.n * z < 2 ^ 64 := by have := hLI.slen; have := hz.n16; omega
  obtain ⟨q, eq⟩ : ∃ q, (σ.gpr .x1).toNat / 2 ^ z = q := ⟨_, rfl⟩
  have hq : q < 2 ^ 32 := eq ▸ Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hidx
  obtain ⟨nd, end_⟩ : ∃ nd, path p pk a 2 0 (σ.gpr .x1).toNat (auth p σ sig) z node0 = nd := ⟨_, rfl⟩
  have X := hP.xk
  have h25 := hP.x25
  have h26 : u.gpr .x26 = BitVec.ofNat 64 q := by rw [hP.x26, eq]
  have hm : bytesAt u.mem (at' S (Layout.laneA 0 + p.n + 32)) (p.n + p.n) =
      (if q % 2 = 0 then nd ++ chunk (auth p σ sig) p.n z else chunk (auth p σ sig) p.n z ++ nd) := by
    rw [hP.msg, eq, end_]
  have eA' := eA
  have hw : (⟨S, 65536⟩ : Region) ∈ u.wr := by rw [X.wr]; exact TreeBase.regions_scr hR
  have hq2 : q / 2 = (σ.gpr .x1).toNat / 2 ^ (z + 1) := by rw [← eq, Nat.div_div_eq_div_mul, Nat.pow_succ]
  refine WP.seq ?_
  rw [← List.append_nil (Impl.SlhDsa.AArch64.setFieldR .x19 _ .x26)]
  refine fieldsA_ok hz X.x19 hw h25 (by omega) h26 hq fun t₈ k₈ f₈ x26₈ b₈ => MlKem.AArch64.wp_nil ?_
  have X₈ : XK p σ S sig pk a D t₈ := XK.step hz X (by decide) k₈ f₈ (aF_safe hz)
  have hm₈ : bytesAt t₈.mem (at' S (Layout.laneA 0 + p.n + 32)) (p.n + p.n) =
      (if q % 2 = 0 then nd ++ chunk (auth p σ sig) p.n z else chunk (auth p σ sig) p.n z ++ nd) := by
    rw [TreeBase.bytesAt_frame f₈ (fun r hr => by
      simp only [aF, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      all_goals exact Offset.disjoint S (by omega) (by rw [eA]; omega) (by rw [eA]; omega)) (by omega), hm]
  refine WP.seq ?_
  rw [ht]
  refine thA_ok hz rfl T f.t4name X₈.x19 (by rw [X₈.wr]; exact TreeBase.regions_scr hR) hfit (.inr rfl)
    fun t₉ r₉ w₉ sp₉ g₉ v₉ b₉ fr₉ => ?_
  have X₉ : XK p σ S sig pk a D t₉ := XK.call hz X₈ r₉ w₉ sp₉ g₉ v₉ fr₉ (t4ch_safe hz)
  refine wp_addi (by decide) fun t₁₀ u₁₀ => wp_subi hh fun t₁₁ u₁₁ => MlKem.AArch64.wp_nil ?_
  have x25₉ : t₉.gpr .x25 = BitVec.ofNat 64 z := by rw [g₉ _ (by decide) (by decide), k₈.get .x25, h25]
  have x26₉ : t₉.gpr .x26 = BitVec.ofNat 64 ((σ.gpr .x1).toNat / 2 ^ (z + 1)) := by
    rw [g₉ _ (by decide) (by decide), x26₈, hq2]
  refine ⟨⟨XK.step hz X₉ (by decide) ((upOnly u₁₀).keep.trans (upOnly u₁₁).keep)
    (by rw [u₁₁.mem, u₁₀.mem]; exact Frame.refl _ _) (fun r hr => absurd hr List.not_mem_nil),
    by rw [u₁₁.other _ (by decide), u₁₀.gpr, x25₉, BitVec.ofNat_add],
    by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), x26₉], ?_⟩,
    by rw [u₁₁.gpr, u₁₀.gpr, x25₉, BitVec.ofNat_add]⟩
  rw [u₁₁.mem, u₁₀.mem, b₉ 0 (by decide)]
  simp only [path]
  rw [end_, H_shake' hz, eq, ← hq2]
  refine congrArg (fun x => shake256 x p.n) ?_
  rw [show 3 * p.n + 32 = p.n + (16 + (16 + (p.n + p.n))) by omega, bytesAt_add, addr_add, bytesAt_add, addr_add,
    bytesAt_add, addr_add]
  rw [X₈.env.seedA 0 (by decide), X₈.env.adrsA 0 (by decide), b₈,
    show Layout.laneA 0 + p.n + 16 + 16 = Layout.laneA 0 + p.n + 32 by omega, hm₈]
  simp only [adrsOf, List.append_assoc]


/-- Height `z` of the path. -/
theorem pathBody_ok (hz : Sz p) (T : Thash4Impl p.n) {f : Impl.SlhDsa.AArch64.Shake.Fns} (ht : f.t4 = T.code)
    {σ : State} {S sig : Addr} {pk a : List Byte} {D : List Nat} {node0 : List Byte}
    (hR : Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32) {z : Nat}
    (hzh : z < p.hp) (hh : p.hp < 4096) {t : State} (hI : PI p σ S sig pk a D node0 z t) :
    WP isa (Impl.SlhDsa.AArch64.Verify.pathBody p f) t fun t' =>
      PI p σ S sig pk a D node0 (z + 1) t' ∧ t'.gpr .x9 = BitVec.ofNat 64 (z + 1) - BitVec.ofNat 64 p.hp :=
  WP.seq (WP.mono (pathB1_ok hz hR hidx hzh hI) fun _ h₁ => WP.seq (WP.mono (pathIte_ok hz hR hidx hzh h₁)
    fun _ h₂ => pathTail_ok hz T ht hR hidx hzh hh h₂))

theorem sub_tab : ∀ a < 11, ∀ b < 11, (BitVec.ofNat 64 a - BitVec.ofNat 64 b != 0) = decide (a ≠ b) := by decide

/-- A pass of the path's loop, at measure `m`, from height `h′ - m`. -/
theorem path_step (hz : Sz p) (T : Thash4Impl p.n) {f : Impl.SlhDsa.AArch64.Shake.Fns} (ht : f.t4 = T.code)
    {σ : State} {S sig : Addr} {pk a : List Byte} {D : List Nat} {node0 : List Byte}
    (hR : Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32) (hh : p.hp ≤ 9)
    (m : Nat) (u : State) (hI : 1 ≤ m ∧ m ≤ p.hp ∧ PI p σ S sig pk a D node0 (p.hp - m) u) :
    WP isa (Impl.SlhDsa.AArch64.Verify.pathBody p f) u fun u' =>
      isa.eval (.nonzero .x .x9) u' = some (decide (m ≠ 1)) ∧
      (decide (m ≠ 1) = false → PI p σ S sig pk a D node0 p.hp u') ∧
      (decide (m ≠ 1) = true → m - 1 < m ∧ (1 ≤ m - 1 ∧ m - 1 ≤ p.hp ∧ PI p σ S sig pk a D node0 (p.hp - (m - 1)) u')) := by
  obtain ⟨h1, h2, hu⟩ := hI
  refine WP.mono (pathBody_ok hz T ht hR hidx (by omega : p.hp - m < p.hp) (by omega) hu) fun u' ⟨hs, h9⟩ =>
    ⟨?_, fun hc => ?_, fun hc => ?_⟩
  · rw [MlKem.AArch64.eval_nonzero, h9, sub_tab _ (by omega) _ (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  · have : m = 1 := by simpa using hc
    subst this
    rwa [show p.hp - 1 + 1 = p.hp by omega] at hs
  · have : m ≠ 1 := by simpa using hc
    exact ⟨by omega, by omega, by omega, by rwa [show p.hp - (m - 1) = p.hp - m + 1 by omega]⟩

/-- The `h′` heights of the path. -/
theorem path_ok (hz : Sz p) (T : Thash4Impl p.n) {f : Impl.SlhDsa.AArch64.Shake.Fns} (ht : f.t4 = T.code)
    {σ t : State} {S sig : Addr} {pk a : List Byte} {D : List Nat} {node0 : List Byte}
    (hR : Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32)
    (hh1 : 1 ≤ p.hp) (hh : p.hp ≤ 9) (hI : PI p σ S sig pk a D node0 0 t) :
    WP isa (.loop (Impl.SlhDsa.AArch64.Verify.pathBody p f) (.nonzero .x .x9)) t (PI p σ S sig pk a D node0 p.hp) :=
  TreeBase.wpLoop _ _ (path_step hz T ht hR hidx hh) p.hp ⟨hh1, Nat.le_refl _, by rw [Nat.sub_self]; exact hI⟩

end VG.Proof.SlhDsa.AArch64.XmssPk
