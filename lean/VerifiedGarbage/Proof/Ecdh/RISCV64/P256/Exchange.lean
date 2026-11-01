module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.Tail
public import VerifiedGarbage.Spec.Ecdh.P256
import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.CheckVerified
import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.CheckLit
public import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.P256.Point

/-!
# ECDH over P-256 on RISC-V: correctness

`vg_ecdh_p256` meets its contract by register (`ecdhRV`), given the group
law (`ecdh_rv`): the setup (`setup_ok`: the saves, `d`, the peer's `x` and
`y` and the mask of its first byte, the constants), the check of the peer's
point (`check_rv`, by its call), the point (or `G`) to `R`'s first two
slots, `tail_ok`, and the result under the flag; the specification's
shared secret is `exchange_eq`'s (`Proof/Ecdh/Exchange.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64.P256

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.P256
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes)

/-- The shared secret of the private key at `d` and the public key at
`peer`, as the specification computes it. -/
abbrev ex (m : Mem) (d peer : Addr) : Option (List Byte) :=
  Spec.Ecdh.exchange Spec.P256.curve (ofBytes (bytesAt m d 32)) (bytesAt m peer 65)

/-- What the contract gives, by register. -/
structure EPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a1, 32⟩, ⟨s.gpr .a2, 65⟩]
  wr : s.wr = [⟨s.gpr .a0, 32⟩, ⟨s.gpr .a3, 8192⟩]
  out : (⟨s.gpr .a0, 32⟩ : Region).Disjoint ⟨s.gpr .a3, 8192⟩
  d : (⟨s.gpr .a1, 32⟩ : Region).Disjoint ⟨s.gpr .a3, 8192⟩
  peer : (⟨s.gpr .a2, 65⟩ : Region).Disjoint ⟨s.gpr .a3, 8192⟩
  fo : (s.gpr .a0).toNat + 32 ≤ 2 ^ 64
  fd : (s.gpr .a1).toNat + 32 ≤ 2 ^ 64
  fp : (s.gpr .a2).toNat + 65 ≤ 2 ^ 64
  fs : (s.gpr .a3).toNat + 8192 ≤ 2 ^ 64
  al : (s.gpr .a3).toNat % 8 = 0

def ecdhRV : Contract isa where
  pre := EPre
  post s s' :=
    match ex s.mem (s.gpr .a1) (s.gpr .a2) with
    | some z => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) 32 = z
    | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) 32 = List.replicate 32 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3

/-- A byte of a region apart from the working space. -/
theorem out_of_disj {p base : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) (hn : p.toNat + n ≤ 2 ^ 64)
    {off i : Nat} (hi : off + i < n) : ¬ (⟨base, 8192⟩ : Region).Contains (p + BitVec.ofNat 64 (off + i)) 1 :=
  hd _ (Offset.contains_base p (by omega) (by omega))

/-- Eight bytes of a region. -/
theorem in_rd8 {rs : List Region} {p : Addr} {n : Nat} (hr : (⟨p, n⟩ : Region) ∈ rs) {off : Nat} (ho : off + 8 ≤ n)
    (hn : n ≤ 8192 := by decide) :
    InRegions rs (p + BitVec.ofNat 64 off) 8 :=
  ⟨_, hr, Offset.contains_base p ho (by omega)⟩

/-- What the setup leaves. -/
structure SetupPost (s s' : State) : Prop where
  ws : WsReg s' (s.gpr .a3)
  s2 : s'.gpr .s2 = s.gpr .a0
  regs : ∀ x, x ≠ .s0 → x ≠ .s2 → x ∈ preserved → s'.gpr x = s.gpr x
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  sv0 : word s'.mem (s.gpr .a3) 0 = s.gpr .s0
  sv1 : word s'.mem (s.gpr .a3) 8 = s.gpr .s1
  sv2 : word s'.mem (s.gpr .a3) 16 = s.gpr .s2
  sv3 : word s'.mem (s.gpr .a3) 24 = s.gpr .ra
  k : sv (s.gpr .a3) s' K = ofBytes (bytesAt s.mem (s.gpr .a1) 32)
  x : sv (s.gpr .a3) s' CX = ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 1) 32)
  y : sv (s.gpr .a3) s' CY = ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 33) 32)
  flag : word s'.mem (s.gpr .a3) FL = maskOf (decide (s.mem (s.gpr .a2) = 4))
  consts : ∀ e ∈ consts p256, sv (s.gpr .a3) s' e.1 = e.2

/-- Bytes apart from the working space survive changes within it. -/
theorem bytesAt_unch {base q : Addr} {W : List (Nat × Nat)} {n : Nat} {m m' : Mem} (U : Unch base W m m')
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ 8192)
    (hsep : ∀ i < n, ¬ (⟨base, 8192⟩ : Region).Contains (q + BitVec.ofNat 64 i) 1) :
    bytesAt m' q n = bytesAt m q n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have := hsep i hi
  simp only [Region.Contains] at this
  exact U _ fun w hw => .inr (by have := hW w hw; simp only [ofs]; omega)

theorem setup_ok {s : State} (hs : EPre s) :
    WP isa (.block (saveCode .a3 ++ loadNum p256.n (p256.sl K) .a1 0 ++ loadNum p256.n (p256.sl CX) .a2 1 ++
      loadNum p256.n (p256.sl CY) .a2 (1 + 8 * p256.n) ++ leadMask .a2 ++ [.store .d .a7 wb (p256.sl FLAG)] ++
      constCode p256)) s fun s' => SetupPost s s' := by
  generalize hb : s.gpr .a3 = base
  have hwr : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hs.wr, ← hb]; simp
  rw [show p256.n = 4 from rfl, show 1 + 8 * 4 = 33 from rfl]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (save_ok hb hwr (by rw [← hb]; exact hs.fs) (by rw [← hb]; exact hs.al))
    fun s₁ ⟨hw₁, o₁, g₁, rd₁, wr₁, sp₁, U₁, w0, w1, w2, w3⟩ => ?_)
  have a1 : s₁.gpr .a1 = s.gpr .a1 := g₁ _ (by decide) (by decide)
  have a2 : s₁.gpr .a2 = s.gpr .a2 := g₁ _ (by decide) (by decide)
  have rd1 : (⟨s.gpr .a1, 32⟩ : Region) ∈ s₁.rd ++ s₁.wr := by rw [rd₁, hs.rd]; simp
  have rd2 : (⟨s.gpr .a2, 65⟩ : Region) ∈ s₁.rd ++ s₁.wr := by rw [rd₁, hs.rd]; simp
  -- `d`.
  refine WP.block_append (WP.mono (loadNum_ok 4 hw₁ (o := p256.sl K) (p := .a1) (off := 0) (by decide) (by decide)
    (by decide) (by decide) (fun j hj => by rw [a1]; exact in_rd8 rd1 (by omega))
    (fun i hi => by rw [a1]; exact out_of_disj (hb ▸ hs.d) hs.fd (by omega)))
    fun s₂ ⟨r₂, O₂, e₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  -- `x` and `y`.
  refine WP.block_append (WP.mono (loadNum_ok 4 hw₂ (o := p256.sl CX) (p := .a2) (off := 1) (by decide) (by decide)
    (by decide) (by decide) (fun j hj => by
      have rd2' : (⟨s.gpr .a2, 65⟩ : Region) ∈ s₂.rd ++ s₂.wr := by rw [r₂.rd, r₂.wr]; exact rd2
      rw [r₂.gpr _ (by decide), a2]; exact in_rd8 rd2' (by omega))
    (fun i hi => by rw [r₂.gpr _ (by decide), a2]; exact out_of_disj (hb ▸ hs.peer) hs.fp (by omega)))
    fun s₃ ⟨r₃, O₃, e₃⟩ => ?_)
  have hw₃ := hw₂.of_rest r₃
  have r₂₃ := r₂.trans r₃
  refine WP.block_append (WP.mono (loadNum_ok 4 hw₃ (o := p256.sl CY) (p := .a2) (off := 33) (by decide) (by decide)
    (by decide) (by decide) (fun j hj => by
      have rd2' : (⟨s.gpr .a2, 65⟩ : Region) ∈ s₃.rd ++ s₃.wr := by rw [r₂₃.rd, r₂₃.wr]; exact rd2
      rw [r₂₃.gpr _ (by decide), a2]; exact in_rd8 rd2' (by omega))
    (fun i hi => by rw [r₂₃.gpr _ (by decide), a2]; exact out_of_disj (hb ▸ hs.peer) hs.fp (by omega)))
    fun s₄ ⟨r₄, O₄, e₄⟩ => ?_)
  have hw₄ := hw₃.of_rest r₄
  have r₂₄ := r₂₃.trans r₄
  -- The first byte, and the flag.
  refine WP.block_append (WP.mono (leadMask_ok (s := s₄) (q := .a2) (by
      rw [r₂₄.rd, r₂₄.wr, r₂₄.gpr _ (by decide), a2]
      exact ⟨_, rd2, by simpa using Offset.contains_base (s.gpr .a2) (d := 0) (n := 1) (k := 65) (by decide) (by decide)⟩))
    fun s₅ ⟨r₅, m₅, g₅⟩ => ?_)
  have hw₅ := hw₄.of_rest r₅
  rw [List.singleton_append]
  refine sd_ws hw₅ (d := p256.sl FLAG) (by decide) (by decide) fun s₆ u₆ => ?_
  have hw₆ := hw₅.of_kp (Kp.of_mupd u₆)
  -- The constants.
  rw [constCode_eq]
  refine WP.mono (consts_ok _ hw₆ consts_slots consts_nodup) fun s₇ ⟨r₇, U₇, e₇⟩ => ?_
  -- What changed.
  have O₆ : Outside base FL 8 s₅.mem s₆.mem := by rw [u₆.mem]; exact writeW_outside _ _ _ (by decide)
  have U₁₇ : Unch base ([(p256.sl K, 8 * 4)] ++ [(p256.sl CX, 8 * 4)] ++ [(p256.sl CY, 8 * 4)] ++ [(FL, 8)] ++
      (consts p256).map fun e => (p256.sl e.1, 32)) s₁.mem s₇.mem :=
    (((O₂.unch.trans O₃.unch).trans O₄.unch).trans (by rw [← m₅]; exact O₆.unch)).trans U₇
  have m₄₆ : Unch base [(FL, 8)] s₄.mem s₆.mem := by rw [← m₅]; exact O₆.unch
  have U₄₇ := m₄₆.trans U₇
  have U₃₇ := O₄.unch.trans U₄₇
  have U₂₇ := O₃.unch.trans U₃₇
  have m₃₁ : Unch base _ s.mem s₃.mem := (U₁.trans O₂.unch).trans O₃.unch
  have hpres : ∀ x ∈ preserved, x ∉ [Reg.t0, .t1, .a7] := by decide
  have hpres' : ∀ x ∈ preserved, x ∉ [Reg.t0, .t1] := by decide
  have gp : ∀ x ∈ preserved, s₇.gpr x = s₁.gpr x := fun x hx => by
    rw [r₇.gpr _ (hpres' x hx), u₆.gpr, r₅.gpr _ (hpres x hx), r₂₄.gpr _ (hpres' x hx)]
  have a2' : s₃.gpr .a2 = s.gpr .a2 := by rw [r₂₃.gpr _ (by decide), a2]
  have a2'' : s₄.gpr .a2 = s.gpr .a2 := by rw [r₂₄.gpr _ (by decide), a2]
  have a1' : s₁.gpr .a1 + BitVec.ofNat 64 0 = s.gpr .a1 := by rw [a1]; simp
  have sep : ∀ {p : Addr} {n : Nat}, (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩ → p.toNat + n ≤ 2 ^ 64 →
      ∀ {off k : Nat}, off + k ≤ n → ∀ i < k,
        ¬ (⟨base, 8192⟩ : Region).Contains (p + BitVec.ofNat 64 off + BitVec.ofNat 64 i) 1 :=
    fun hd hn _ _ hk i hi => by
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact out_of_disj hd hn (by omega)
  subst hb
  refine ⟨hw₆.of_rest r₇, ?_, fun x h0 h2 hx => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gp _ (by decide), o₁]
  · rw [gp _ hx, g₁ _ h0 h2]
  · rw [r₇.rd, u₆.rd, r₅.rd, r₂₄.rd, rd₁]
  · rw [r₇.wr, u₆.wr, r₅.wr, r₂₄.wr, wr₁]
  · rw [r₇.sp, u₆.sp, r₅.sp, r₂₄.sp, sp₁]
  · rw [U₁₇.word (by decide) (by decide)]; exact w0
  · rw [U₁₇.word (by decide) (by decide)]; exact w1
  · rw [U₁₇.word (by decide) (by decide)]; exact w2
  · rw [U₁₇.word (by decide) (by decide)]; exact w3
  · show wordsVal _ _ _ _ = _
    rw [sv_unch U₂₇ K (by decide), e₂, a1', bytesAt_unch U₁ (by decide) (by simpa using sep hs.d hs.fd (off := 0) (k := 32) (by omega))]
  · show wordsVal _ _ _ _ = _
    rw [sv_unch U₃₇ CX (by decide), e₃, r₂.gpr _ (by decide), a2,
      bytesAt_unch (U₁.trans O₂.unch) (by decide) (sep hs.peer hs.fp (off := 1) (k := 32) (by omega))]
  · show wordsVal _ _ _ _ = _
    rw [sv_unch U₄₇ CY (by decide), e₄, a2', bytesAt_unch m₃₁ (by decide) (sep hs.peer hs.fp (off := 33) (k := 32) (by omega))]
  · rw [U₇.word (by decide) (by decide), u₆.mem, sl_FLAG, word_writeW_self, g₅, a2'']
    have h1 := bytesAt_unch (m₃₁.trans O₄.unch) (q := s.gpr .a2) (n := 1) (by decide)
      (by simpa using sep hs.peer hs.fp (off := 0) (k := 1) (by omega))
    simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h1
    simp only [BitVec.add_zero] at h1
    rw [h1]
  · intro e he
    rw [e₇ e he, Nat.mod_eq_of_lt (consts_lt e he)]

/-- The value of a constant's slot. -/
theorem const_at {base : Addr} {s : State} (hc : ∀ e ∈ consts p256, sv base s e.1 = e.2) (k : Nat)
    (hk : k < (consts p256).length := by decide) : sv base s (consts p256)[k].1 = (consts p256)[k].2 :=
  hc _ (List.getElem_mem hk)

/-- The check of the peer's point, by its call. -/
theorem check_ok {s : State} {base : Addr} (hw : WsReg s base) (hc : ∀ e ∈ consts p256, sv base s e.1 = e.2)
    (hf : word s.mem base FL = 0 ∨ word s.mem base FL = BitVec.allOnes 64) :
    WP isa (wsCall Spec.Weierstrass.CheckPoint.p256.checkApi.name checkP256) s fun s' =>
      Kp s s' ∧ Unch base checkKW s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&&
        Spec.Weierstrass.CheckPoint.Curve.mask (CC.Valid (sv base s CX) (sv base s CY)) ∧
      sv base s' CPX = (if word s'.mem base FL = 0 then sv base s GX else sv base s CX * 2 ^ 256 % W.p) ∧
      sv base s' CPY = (if word s'.mem base FL = 0 then sv base s GY else sv base s CY * 2 ^ 256 % W.p) := by
  refine wsCall_ok checkP256_noFrames check_rv hw (fun t r w a m => ?_) fun s' K t a m hp => ?_
  · refine ⟨r, by rw [w, a], by rw [a]; exact hw.nowrap, by rw [a]; exact hw.al, ?_⟩
    rw [a, m]
    refine ⟨(num_eq _ _ MP).trans (const_at hc 0), (num_eq _ _ R2P).trans (const_at hc 10),
      (num_eq _ _ AP).trans (const_at hc 5), (num_eq _ _ BP).trans (const_at hc 11), ?_⟩
    rw [flag_eq]; exact hf
  · have hp' : CC.post base s.mem s'.mem := by
      have := hp
      simp only [checkRVc, State.withRegions_mem] at this
      rw [a, m] at this
      exact this
    obtain ⟨hF, -, -, hx, hy, hK⟩ := hp'
    have ex : CC.num base s.mem CC.xAt = sv base s CX := num_eq _ _ CX
    have ey : CC.num base s.mem CC.yAt = sv base s CY := num_eq _ _ CY
    have egx : CC.num base s.mem CC.gxAt = sv base s GX := num_eq _ _ GX
    have egy : CC.num base s.mem CC.gyAt = sv base s GY := num_eq _ _ GY
    have epx : CC.num base s'.mem CC.pxAt = sv base s' CPX := num_eq _ _ CPX
    have epy : CC.num base s'.mem CC.pyAt = sv base s' CPY := num_eq _ _ CPY
    rw [flag_eq, flag_eq, ex, ey] at hF
    rw [ex, ey, egx, flag_eq, epx, ← hF] at hx
    rw [ex, ey, egy, flag_eq, epy, ← hF] at hy
    exact ⟨K, unch_of_checkKeeps hK, hF, hx, hy⟩

/-- The bytes just written. -/
theorem bytesAt_writeBytes (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length ≤ 2 ^ 64) :
    bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i h₁ h₂
    have hi : i < xs.length := h₂
    simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes,
      Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hi h), hi,
      ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem and_one (b : Bool) : maskOf b &&& BitVec.ofInt 64 1 = if b then 1 else 0 := by cases b <;> decide

/-- The end: the flag `&=` the mask of `Z ≠ 0`, `x` (or zeros) to `out`, the
flag's low bit to `a0`, and the saved registers restored. -/
theorem fin_ok {s : State} {base out : Addr} (hw : WsReg s base) (h2 : s.gpr .s2 = out)
    (hout : ∀ i < 32, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < 32, ¬ (⟨base, 8192⟩ : Region).Contains (out + BitVec.ofNat 64 i) 1)
    {c : Bool} (hF : word s.mem base FL = maskOf c) :
    WP isa (.block (zCode p256 ++ storeNum p256.n (p256.sl XO) .s2 0 ++ retCode p256)) s fun s' =>
      s'.gpr .a0 = (if c && !decide (sv base s RZ = 0) then 1 else 0) ∧
      bytesAt s'.mem out 32 = toBytes 32 (if c && !decide (sv base s RZ = 0) then sv base s XO else 0) ∧
      s'.gpr .s0 = word s.mem base 0 ∧ s'.gpr .s1 = word s.mem base 8 ∧ s'.gpr .s2 = word s.mem base 16 ∧
      s'.gpr .ra = word s.mem base 24 ∧
      (∀ r ∈ preserved, r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp := by
  rw [zCode, retCode, restoreCode, show p256.n = 4 from rfl]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (zeroMask_ok hw (n := 4) (a := p256.sl RZ) (by decide) (by decide))
    fun s₁ ⟨r₁, m₁, g₁⟩ => ?_)
  rw [List.singleton_append]
  refine WP.cons (exec_logicImm (by decide)) ?_
  have r₁' := r₁.trans ((Upd.write s₁ .a7 (s₁.gpr .a7 ^^^ BitVec.ofInt 64 (-1))).rest (ws := [.t3, .t4, .a7])
    (by decide))
  have hw₁ := hw.of_rest r₁'
  refine WP.block_append (WP.mono (andFlag_ok hw₁) fun s₂ ⟨f₂, r₂, O₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  rw [List.singleton_append]
  refine ld_ws hw₂ (d := p256.sl FLAG) (by decide) (by decide) fun s₃ u₃ => ?_
  have hw₃ := hw₂.of_kp (Kp.of_upd u₃)
  -- The flag.
  have hb : word s₂.mem base FL = maskOf (c && !decide (sv base s RZ = 0)) := by
    rw [f₂]
    simp only [State.write, ↓reduceIte]
    rw [m₁, hF, g₁, not_mask, maskOf_and]
  have a₃ : s₃.gpr .a7 = maskOf (c && !decide (sv base s RZ = 0)) := by rw [u₃.gpr, sl_FLAG]; exact hb
  have xo : wordsVal s₃.mem base (p256.sl XO) 4 = sv base s XO := by
    rw [u₃.mem, O₂.wordsVal (by decide) (by decide)]
    show wordsVal (s₁.write _ _).mem _ _ _ = _
    simp only [State.write]; rw [m₁]
  have q₃ : s₃.gpr .s2 = out := by
    rw [u₃.other _ (by decide), r₂.gpr _ (by decide), r₁'.gpr _ (by decide), h2]
  refine WP.block_append (WP.mono (storeNum_ok _ 4 hw₃ a₃ (q := .s2) (a := p256.sl XO) (off := 0) (by decide)
    (by decide) (by decide) (by decide)
    (fun i hi => by rw [q₃, Nat.zero_add, u₃.wr, r₂.wr, r₁'.wr]; exact hout i hi)
    (fun i hi => by rw [q₃, Nat.zero_add]; exact hsep i hi)) fun s₄ ⟨r₄, m₄⟩ => ?_)
  have hw₄ := hw₃.of_rest r₄
  have U₄ : Unch base [(8192, 2 ^ 64)] s₃.mem s₄.mem := by
    rw [m₄]; exact writeBytes_unch _ fun i hi => by
      rw [q₃, BitVec.add_zero]
      exact hsep i (by simpa [VG.Proof.Weierstrass.length_toBytes] using hi)
  have wd : ∀ d, d + 8 ≤ 2048 → d + 8 ≤ FL ∨ FL + 8 ≤ d → word s₄.mem base d = word s.mem base d := fun d hd h => by
    rw [U₄.word (by simp; omega) (by omega), u₃.mem, O₂.word h (by omega)]
    show word (s₁.write _ _).mem _ _ = _
    simp only [State.write]; rw [m₁]
  -- The return value and the restores.
  refine ld_ws hw₄ (d := p256.sl FLAG) (by decide) (by decide) fun s₅ u₅ => ?_
  refine WP.cons (exec_logicImm (by decide)) ?_
  have u₅' := Upd.write s₅ .a0 (s₅.gpr .a0 &&& BitVec.ofInt 64 1)
  have hw₅ := (hw₄.of_kp (Kp.of_upd u₅)).of_kp (Kp.of_upd u₅')
  refine ld_ws hw₅ (d := 24) (by decide) (by decide) fun s₆ u₆ => ?_
  have hw₆ := hw₅.of_kp (Kp.of_upd u₆)
  refine ld_ws hw₆ (d := 16) (by decide) (by decide) fun s₇ u₇ => ?_
  have hw₇ : WsReg s₇ base := ⟨by rw [u₇.other _ (by decide)]; exact hw₆.s0, by rw [u₇.wr]; exact hw₆.wr,
    hw₆.nowrap, hw₆.al⟩
  refine ld_ws hw₇ (d := 8) (by decide) (by decide) fun s₈ u₈ => ?_
  have hw₈ : WsReg s₈ base := ⟨by rw [u₈.other _ (by decide)]; exact hw₇.s0, by rw [u₈.wr]; exact hw₇.wr,
    hw₇.nowrap, hw₇.al⟩
  refine ld_ws hw₈ (d := 0) (by decide) (by decide) fun s₉ u₉ => WP.block_nil ?_
  have m₉ : s₉.mem = s₄.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅'.mem, u₅.mem]
  have fl₄ : word s₄.mem base FL = maskOf (c && !decide (sv base s RZ = 0)) := by
    rw [U₄.word (by decide) (by decide), u₃.mem, hb]
  have np : ∀ r ∈ preserved, r ∉ [Reg.t0, .t1, .t3, .t4, .a7, .a0, .ra] := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅'.gpr,
      u₅.gpr, sl_FLAG, fl₄, and_one]
  · have hl : (toBytes 32 (if (c && !decide (sv base s RZ = 0)) = true then sv base s XO else 0)).length = 32 :=
      VG.Proof.Weierstrass.length_toBytes _ _
    rw [m₉, m₄, q₃, BitVec.add_zero, xo]
    have := bytesAt_writeBytes s₃.mem out _ (by rw [hl]; decide)
    rwa [hl] at this
  · rw [u₉.gpr, u₈.mem, u₇.mem, u₆.mem, u₅'.mem, u₅.mem,
      wd 0 (by decide) (by decide)]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.mem, u₆.mem, u₅'.mem, u₅.mem, wd 8 (by decide) (by decide)]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.mem, u₅'.mem, u₅.mem,
      wd 16 (by decide) (by decide)]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅'.mem, u₅.mem,
      wd 24 (by decide) (by decide)]
  · intro r hr h0 h1 h2'
    have hn := np r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rw [u₉.other _ h0, u₈.other _ h1, u₇.other _ h2', u₆.other _ hn.2.2.2.2.2.2, u₅'.other _ hn.2.2.2.2.2.1,
      u₅.other _ hn.2.2.2.2.2.1, r₄.gpr _ (by simp [hn.1, hn.2.1]), u₃.other _ hn.2.2.2.2.1,
      r₂.gpr _ (by simp [hn.1]), r₁'.gpr _ (by simp [hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1])]
  · rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅'.sp, u₅.sp, r₄.sp, u₃.sp, r₂.sp, r₁'.sp]

/-- The peer's key: `04`, `x` and `y`. -/
theorem peer_bytes (m : Mem) (p : Addr) (L : Nat) :
    bytesAt m p (1 + 2 * L) = m p :: (bytesAt m (p + BitVec.ofNat 64 1) L ++
      bytesAt m (p + BitVec.ofNat 64 (1 + L)) L) := by
  have h1 : bytesAt m p 1 = [m p] := by
    simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero]
  rw [show 1 + 2 * L = 1 + (L + L) by omega, VG.Proof.Weierstrass.bytesAt_add,
    VG.Proof.Weierstrass.bytesAt_add, h1, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rfl

theorem exchange_none {C : Curve} {d : Nat} (bs : List Byte) (h : ¬ (1 ≤ d ∧ d < C.n)) :
    Spec.Ecdh.exchange C d bs = none := by
  unfold Spec.Ecdh.exchange; simp only [h, ↓reduceIte]

theorem mask_eq (P : Prop) [Decidable P] : Spec.Weierstrass.CheckPoint.Curve.mask P = maskOf (decide P) := by
  unfold Spec.Weierstrass.CheckPoint.Curve.mask maskOf; by_cases h : P <;> simp [h]

/-- The check's validity is the specification's, but for the first byte. -/
theorem valid_iff (x y : Nat) :
    CC.Valid x y ↔ x < W.p ∧ y < W.p ∧ VG.Proof.Ecdh.OnCurveF W x y := by
  unfold Spec.Weierstrass.CheckPoint.Curve.Valid
  constructor
  · rintro ⟨hx, hy, h⟩
    refine ⟨hx, hy, (VG.Proof.Ecdh.onCurve_iff hx hy).mp ?_⟩
    rw [VG.Proof.EcKey.fe_eq hx rfl, VG.Proof.EcKey.fe_eq hy rfl] at h; exact h
  · rintro ⟨hx, hy, h⟩
    refine ⟨hx, hy, ?_⟩
    have := (VG.Proof.Ecdh.onCurve_iff hx hy).mpr h
    show Spec.Weierstrass.onCurve W (.affine (Fin.ofNat W.p x) (Fin.ofNat W.p y)) = true
    rw [VG.Proof.EcKey.fe_eq hx rfl, VG.Proof.EcKey.fe_eq hy rfl]; exact this

/-- `vg_ecdh_p256` by register. -/
theorem ecdh_ok (hL : VG.Proof.Weierstrass.Law W) {s : State} (hs : EPre s) :
    WP isa ecdhP256 s fun s' => abiPreserved s s' ∧ ecdhRV.post s s' := by
  have hp0 : 0 < W.p := by decide
  rw [ecdhP256, Cfg.ecdhFn]
  refine WP.seq (WP.mono (setup_ok hs) fun s₁ S => ?_)
  obtain ⟨hw₁, S2, Sregs, Srd, Swr, Ssp, Ssv0, Ssv1, Ssv2, Ssv3, Sk, Sx, Sy, Sflag, Scs⟩ := S
  generalize hb : s.gpr .a3 = base at hw₁ Ssv0 Ssv1 Ssv2 Ssv3 Sk Sx Sy Sflag Scs
  -- The check.
  have hf₁ : word s₁.mem base FL = 0 ∨ word s₁.mem base FL = BitVec.allOnes 64 := by
    rw [Sflag]; unfold maskOf; split <;> simp
  refine WP.seq (WP.mono (check_ok hw₁ Scs hf₁) fun s₂ ⟨K₂, U₂, f₂, px₂, py₂⟩ => ?_)
  have hw₂ := hw₁.of_kp K₂
  -- The point to `R`.
  rw [show p256.n = 4 from rfl]
  refine WP.seq (WP.block_append (WP.mono (copy_ok 4 hw₂ (o := p256.sl RX) (a := p256.sl CPX) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₃ ⟨v₃, r₃, O₃⟩ =>
    WP.mono (copy_ok 4 (hw₂.of_rest r₃) (o := p256.sl RY) (a := p256.sl CPY) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₄ ⟨v₄, r₄, O₄⟩ => ?_))
  have hw₄ := (hw₂.of_rest r₃).of_rest r₄
  have U₁₄ := (U₂.trans O₃.unch).trans O₄.unch
  have tc₁ : TailConsts base s₁ := ⟨const_at Scs 0, const_at Scs 1, const_at Scs 2, const_at Scs 3,
    const_at Scs 4, const_at Scs 5, const_at Scs 6, const_at Scs 9⟩
  have tc₄ := tc₁.of_unch U₁₄ (by decide)
  have gx₁ : sv base s₁ GX = W.gx * 2 ^ 256 % W.p := const_at Scs 7
  have gy₁ : sv base s₁ GY = W.gy * 2 ^ 256 % W.p := const_at Scs 8
  have rx₄ : sv base s₄ RX = sv base s₂ CPX := by
    show wordsVal _ _ _ _ = _
    rw [O₄.wordsVal (by decide) (by decide)]; exact v₃
  have ry₄ : sv base s₄ RY = sv base s₂ CPY := by
    show wordsVal _ _ _ _ = _
    rw [v₄, O₃.wordsVal (by decide) (by decide)]
  generalize hF : word s₂.mem base FL = F at px₂ py₂ f₂
  generalize hx : sv base s₁ CX = x at Sx px₂ py₂ f₂
  generalize hy : sv base s₁ CY = y at Sy px₂ py₂ f₂
  have hval : F ≠ 0 → CC.Valid x y := fun h0 => by
    by_contra h
    apply h0
    rw [f₂, mask_eq, decide_eq_false h]
    exact BitVec.and_zero
  have lt_rx : sv base s₄ RX < W.p := by
    rw [rx₄, px₂]; split
    · rw [gx₁]; exact Nat.mod_lt _ hp0
    · exact Nat.mod_lt _ hp0
  have lt_ry : sv base s₄ RY < W.p := by
    rw [ry₄, py₂]; split
    · rw [gy₁]; exact Nat.mod_lt _ hp0
    · exact Nat.mod_lt _ hp0
  have hon : Spec.Weierstrass.onCurve W (.affine (toM W.p (2 ^ 256) (sv base s₄ RX))
      (toM W.p (2 ^ 256) (sv base s₄ RY))) = true := by
    rw [rx₄, ry₄, px₂, py₂]
    by_cases h0 : F = 0
    · rw [ite_eq_left h0, ite_eq_left h0, gx₁, gy₁, toM_mont unit, toM_mont unit]
      exact VG.Proof.P256.onCurve_G
    · rw [ite_eq_right h0, ite_eq_right h0, toM_mont unit, toM_mont unit]
      exact (hval h0).2.2
  refine WP.seq (WP.mono (tail_ok hL hw₄ tc₄ lt_rx lt_ry hon) fun s₅ ⟨Kc₅, U₅, f₅, rep₅, xolt, xoeq⟩ => ?_)
  have hw₅ := hw₄.of_kc Kc₅
  have h2 : s₅.gpr .s2 = s.gpr .a0 := by
    rw [Kc₅.gpr _ (by decide) (by decide), r₄.gpr _ (by decide), r₃.gpr _ (by decide), K₂.gpr _ (by decide), S2]
  have wr₅ : s₅.wr = s.wr := by rw [Kc₅.wr, r₄.wr, r₃.wr, K₂.wr, Swr]
  have fl₄ : word s₄.mem base FL = F := by
    rw [O₄.word (by decide) (by decide), O₃.word (by decide) (by decide), hF]
  have k₄ : sv base s₄ K = ofBytes (bytesAt s.mem (s.gpr .a1) 32) := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch U₁₄ K (by decide)]; exact Sk
  refine WP.mono (fin_ok hw₅ h2 (fun i hi => by
      rw [wr₅, hs.wr]
      exact ⟨_, List.mem_cons_self .., Offset.contains_base (s.gpr .a0) (d := i) (n := 1) (k := 32) (by omega)
        (by omega)⟩)
    (fun i hi => by
      have := out_of_disj (hb ▸ hs.out) hs.fo (off := 0) (i := i) (by omega); rwa [Nat.zero_add] at this)
    (c := (((decide (s.mem (s.gpr .a2) = 4) && decide (CC.Valid x y)) &&
      decide (ofBytes (bytesAt s.mem (s.gpr .a1) 32) < W.n)) && !decide (ofBytes (bytesAt s.mem (s.gpr .a1) 32) = 0)))
    (by rw [f₅, fl₄, f₂, Sflag, mask_eq, k₄, maskOf_and, maskOf_and, maskOf_and]))
    fun s' ⟨a0', bytes', s0', s1', s2', ra', regs', sp'⟩ => ?_
  have U₁₅ := U₁₄.trans U₅
  -- The registers.
  refine ⟨⟨fun r hr => ?_, by rw [sp', Kc₅.sp, r₄.sp, r₃.sp, K₂.sp, Ssp],
    by rw [ra', U₁₅.word (by decide) (by decide), Ssv3]⟩, ?_⟩
  · by_cases h0 : r = .s0
    · subst h0; rw [s0', U₁₅.word (by decide) (by decide), Ssv0]
    by_cases h1 : r = .s1
    · subst h1; rw [s1', U₁₅.word (by decide) (by decide), Ssv1]
    by_cases h2' : r = .s2
    · subst h2'; rw [s2', U₁₅.word (by decide) (by decide), Ssv2]
    have ht : r ∉ [Reg.t0] := by rintro h; simp only [List.mem_singleton] at h; subst h; exact absurd hr (by decide)
    rw [regs' r hr h0 h1 h2', Kc₅.gpr r hr h1, r₄.gpr r ht, r₃.gpr r ht, K₂.gpr r hr, Sregs r h0 h2' hr]
  -- The specification.
  generalize hD : ofBytes (bytesAt s.mem (s.gpr .a1) 32) = D at k₄ a0' bytes'
  generalize hb0 : s.mem (s.gpr .a2) = b0 at a0' bytes' Sflag
  rw [k₄] at rep₅
  have hlen : (bytesAt s.mem (s.gpr .a2) 65).length = 2 * W.len + 1 := VG.Proof.Weierstrass.length_bytesAt _ _ _
  have hpb := peer_bytes s.mem (s.gpr .a2) 32
  have hhd : (bytesAt s.mem (s.gpr .a2) 65).head? = some b0 := by rw [hpb, ← hb0]; rfl
  have hxv : ofBytes (((bytesAt s.mem (s.gpr .a2) 65).drop 1).take W.len) = x := by
    rw [show W.len = 32 from rfl, hpb, List.drop_one, List.tail_cons,
      List.take_left' (VG.Proof.Weierstrass.length_bytesAt _ _ _)]; exact Sx.symm
  have hyv : ofBytes ((bytesAt s.mem (s.gpr .a2) 65).drop (W.len + 1)) = y := by
    rw [show W.len = 32 from rfl, hpb, List.drop_succ_cons, List.drop_left' (VG.Proof.Weierstrass.length_bytesAt _ _ _)]; exact Sy.symm
  have hex : ex s.mem (s.gpr .a1) (s.gpr .a2) = Spec.Ecdh.exchange W D (bytesAt s.mem (s.gpr .a2) 65) := by
    rw [← hD]
  unfold ecdhRV
  simp only
  rw [hex]
  by_cases hd : 1 ≤ D ∧ D < W.n
  · obtain ⟨hR, -, -, rzlt⟩ := rep₅ hd.1 hd.2
    have hP : ∀ h : VG.Proof.Ecdh.Valid W b0 x y,
        Point.affine (toM W.p (2 ^ 256) (sv base s₄ RX)) (toM W.p (2 ^ 256) (sv base s₄ RY)) =
          .affine ⟨x, h.2.1⟩ ⟨y, h.2.2.1⟩ := fun h => by
      have hv : CC.Valid x y := (valid_iff x y).mpr h.2
      have hF0 : F ≠ 0 := by
        rw [f₂, Sflag, mask_eq, decide_eq_true h.1, decide_eq_true hv]; decide
      rw [rx₄, ry₄, px₂, py₂, ite_eq_right hF0, ite_eq_right hF0, toM_mont unit, toM_mont unit,
        VG.Proof.EcKey.fe_eq h.2.1 rfl, VG.Proof.EcKey.fe_eq h.2.2.1 rfl]
    rw [VG.Proof.Ecdh.exchange_eq hL hlen hhd hxv hyv hP hR xolt xoeq]
    have key : ((((decide (b0 = 4) && decide (CC.Valid x y)) && decide (D < W.n)) && !decide (D = 0)) &&
        !decide (sv base s₅ RZ = 0)) = true ↔
        (1 ≤ D ∧ D < W.n) ∧ VG.Proof.Ecdh.Valid W b0 x y ∧ toM W.p (2 ^ 256) (sv base s₅ RZ) ≠ 0 := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      rw [ne_eq, toM_eq_zero_iff unit rzlt, valid_iff]
      unfold VG.Proof.Ecdh.Valid
      constructor
      · rintro ⟨⟨⟨⟨h4, hv⟩, hn⟩, hz⟩, hr⟩; exact ⟨⟨by omega, hn⟩, ⟨h4, hv⟩, hr⟩
      · rintro ⟨⟨h1, hn⟩, ⟨h4, hv⟩, hr⟩; exact ⟨⟨⟨⟨h4, hv⟩, hn⟩, by omega⟩, hr⟩
    by_cases hc : (1 ≤ D ∧ D < W.n) ∧ VG.Proof.Ecdh.Valid W b0 x y ∧ toM W.p (2 ^ 256) (sv base s₅ RZ) ≠ 0
    · have hb := key.mpr hc
      rw [ite_eq_left hc]
      rw [hb] at a0' bytes'
      exact ⟨a0', bytes'⟩
    · have hb : ((((decide (b0 = 4) && decide (CC.Valid x y)) && decide (D < W.n)) && !decide (D = 0)) &&
          !decide (sv base s₅ RZ = 0)) = false := by
        cases h : ((((decide (b0 = 4) && decide (CC.Valid x y)) && decide (D < W.n)) && !decide (D = 0)) &&
          !decide (sv base s₅ RZ = 0))
        · rfl
        · exact absurd (key.mp h) hc
      rw [ite_eq_right hc]
      rw [hb] at a0' bytes'
      exact ⟨a0', bytes'.trans (by rw [ite_eq_right Bool.false_ne_true]; decide)⟩
  · rw [exchange_none _ hd]
    have hb : ((((decide (b0 = 4) && decide (CC.Valid x y)) && decide (D < W.n)) && !decide (D = 0)) &&
        !decide (sv base s₅ RZ = 0)) = false := by
      by_cases hn : D < W.n
      · have : D = 0 := by omega
        simp [this]
      · simp [hn]
    rw [hb] at a0' bytes'
    exact ⟨a0', bytes'.trans (by rw [ite_eq_right Bool.false_ne_true]; decide)⟩

theorem ecdh_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : ecdhRV.pre s) :
    ∃ t s', Exec isa ecdhP256 s t s' ∧ abiPreserved s s' ∧ ecdhRV.post s s' := by
  obtain ⟨t, s', he, h⟩ := ecdh_ok hL hs
  exact ⟨t, s', he, h⟩

end VG.Proof.Ecdh.RISCV64.P256
