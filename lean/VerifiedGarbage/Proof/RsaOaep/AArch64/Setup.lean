module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.CtBase
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Args
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Tier
public import VerifiedGarbage.Spec.RsaOaep.AnyHash
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.CtBase
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# RSAES-OAEP on AArch64: the hash functions' slots

`selArg hs j sel len` stores the number `k` of a hash function, our stack
argument `j`, in the slot `sel`, and the `hLen` of the `k`th of `hs` in the
slot `len`, by a dispatch whose cases are constants (`selArg_ok`), in the
same time for any two runs with the same number (`selArg_tr`).

`hs` is a tier's hash functions (`Tier`): for each of the numbers the
functions take (`Spec.RsaOaep.hashIds`), its hash function `v` is the one
the number names (`tier_num`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs cases)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash Tier)

/-! ## The tier's hash functions -/

/-- The implementation of each hash function of a tier. -/
def tierHs (t : Tier) : List Hash := t.hashes.map (·.H)

theorem tier_len (t : Tier) : t.hashes.length = 8 := by
  have := congrArg List.length t.mgf_ok
  simpa using this

/-- The hash function `k` names, for `k` one of the numbers the functions
take: `v` of the tier, which is `HashId.mgf1 k`. -/
theorem tier_num (t : Tier) {k : Nat} (hk : k ∈ Spec.RsaOaep.hashIds) :
    ∃ v : MdHash, Num (tierHs t) k v.H ∧ Spec.HashId.mgf1 k = some v.mgf.G := by
  have hk' : 1 ≤ k ∧ k ≤ 7 := by
    simp only [Spec.RsaOaep.hashIds, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
  have hl := tier_len t
  refine ⟨t.hashes[k]'(by omega), ⟨by simp [tierHs, hl], hk'.1, hk'.2, by
    simp only [tierHs, List.getElem?_map, List.getElem?_eq_getElem (show k < t.hashes.length by omega),
      Option.map_some]⟩, ?_⟩
  have := congrArg (·[k]?) t.mgf_ok
  simp only [List.getElem?_map, List.getElem?_range (show k < 8 by omega), Option.map_some] at this
  rw [List.getElem?_eq_getElem (by omega)] at this
  exact (Option.some.inj this).symm ▸ rfl

/-- MGF1's hash function, as a hash function of `MdHash` takes it, is valid. -/
theorem mgf_valid {H : Hash} {hH : Proof.Pbkdf2.Md.AArch64.HashOK H} (lk : Proof.Pbkdf2.Md.AArch64.MgfLink H hH) :
    Proof.Mgf1.Valid lk.G := by
  have hD := hH.sizes.D0
  refine ⟨by rw [lk.len]; exact hD, fun x => ?_⟩
  rw [lk.hash, hH.hash, List.length_take, MdStream.Md.hash, hH.md.digest_length, lk.len]
  have := hH.sizes.DN
  omega

/-- The `hLen` of the `k`th hash function of `hs` (0 if there is none). -/
def lenAt (hs : List Hash) (k : Nat) : Nat := (hs[k]?.map (·.D)).getD 0

theorem Num.lenAt {hs : List Hash} {k : Nat} {G : Hash} (h : Num hs k G) : lenAt hs k = G.D := by
  rw [AArch64.lenAt, h.get]; rfl

/-! ## The number and its length to their slots -/

/-- The number to its slot, and in `x16`. -/
theorem selHead_ok {u : State} {F S : Addr} (L : Lay u F S) {j sel k : Nat}
    (hj : arg j % 8 = 0 ∧ arg j < 32768) (hsel : sel % 8 = 0 ∧ sel + 8 ≤ frameBytes)
    (hld : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 (arg j)) 8)
    (hv : u.mem.read (F + BitVec.ofNat 64 (arg j)) 8 = BitVec.ofNat 64 k) :
    WP isa (.block [.ldrSp .x16 (arg j), .addSp .x9 0, .str .x .x16 .x9 sel]) u fun u' =>
      u'.sp = u.sp ∧ u'.gpr .x16 = BitVec.ofNat 64 k := by
  have ws : InRegions u.wr (F + BitVec.ofNat 64 sel) 8 := L.st hsel.2
  have hs8 : sel < 32768 := by unfold frameBytes at hsel; omega
  oaep_run [L.sp, hld, hv, hj.1, hj.2, hsel.1, hs8, ws, BitVec.add_zero]

theorem selArg_ok {hs : List Hash} {k : Nat} {G : Hash} (hn : Num hs k G) (hD : G.D < 65536)
    {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W)
    {j a b : Nat} (ha : a < nW) (hb : b < nW) (ha12 : a ≠ 12) (hb12 : b ≠ 12)
    (hj : arg j % 8 = 0 ∧ arg j < 32768)
    (hld : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 (arg j)) 8)
    (hv : u.mem.read (F + BitVec.ofNat 64 (arg j)) 8 = BitVec.ofNat 64 k) (ws : List Region) :
    WP isa (selArg hs j (8 * a) (8 * b)) u fun u' => Lay u' F S ∧ Step F S ws u u' ∧
      Rep u'.mem F S V (upd (upd W a (BitVec.ofNat 64 k)) b (BitVec.ofNat 64 G.D)) := by
  have G' := L.geo
  have R1 : Rep (u.mem.write (off F (8 * a)) 8 (BitVec.ofNat 64 k)) F S V (upd W a (BitVec.ofNat 64 k)) :=
    R.wq G' ha _
  have wa : InRegions u.wr (F + BitVec.ofNat 64 (8 * a)) 8 := L.st (by unfold nW frameBytes at *; omega)
  have ha8 : 8 * a % 8 = 0 ∧ 8 * a < 32768 := by unfold nW frameBytes at *; omega
  have hb8 : 8 * b % 8 = 0 ∧ 8 * b < 32768 := by unfold nW frameBytes at *; omega
  unfold selArg seqs seqs
  refine WP.seq (WP.mono (Q := fun (u1 : State) => u1.mem = u.mem.write (off F (8 * a)) 8 (BitVec.ofNat 64 k) ∧
      u1.rd = u.rd ∧ u1.wr = u.wr ∧ u1.sp = u.sp ∧ u1.v = u.v ∧
      (∀ r ∈ preserved, r ≠ .x30 → u1.gpr r = u.gpr r) ∧
      u1.gpr .x16 = BitVec.ofNat 64 k) ?_ fun u1 ⟨hm, hrd, hwr, hsp, hv1, hcs, x16⟩ => ?_)
  · oaep_run [L.sp, hld, hv, hj.1, hj.2, ha8.1, ha8.2, wa, BitVec.add_zero]
    oaep_fin
  have L1 : Lay u1 F S := L.congr hsp hwr (by
    rw [hm, show sScr = 8 * 12 from rfl, R1.fr 12 (by decide), R.fr 12 (by decide), upd, ifn (Ne.symm ha12)])
  have R1' : Rep u1.mem F S V (upd W a (BitVec.ofNat 64 k)) := hm ▸ R1
  have S1 : Step F S ws u u1 := ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv1], by
    rw [hm]; exact Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _ (cF F (by unfold nW frameBytes at *; omega))⟩
  have hpres : ∀ r ∈ preserved, r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x16 ∧ r ≠ .x17 := by
    intro r hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine WP.seq (chain_wp hn _ x16 fun u2 hu2 => ?_)
  refine WP.mono (Q := fun (u3 : State) => u3.mem = u1.mem ∧ u3.rd = u1.rd ∧ u3.wr = u1.wr ∧ u3.sp = u1.sp ∧
      u3.v = u1.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u3.gpr r = u1.gpr r) ∧
      u3.gpr .x10 = BitVec.ofNat 64 G.D) ?_ fun u3 ⟨hm3, hrd3, hwr3, hsp3, hv3, hcs3, x10⟩ => ?_
  · oaep_run [imm16 hD, hu2.mem, hu2.rd, hu2.wr, hu2.sp, hu2.v]
    refine ⟨trivial, trivial, trivial, trivial, trivial, fun r hr _ => ?_, trivial⟩
    obtain ⟨_, h10, h16, h17⟩ := hpres r hr
    rw [ifn h10]; exact hu2.gpr r h16 h17
  have R2 : Rep ((u.mem.write (off F (8 * a)) 8 (BitVec.ofNat 64 k)).write (off F (8 * b)) 8 (BitVec.ofNat 64 G.D))
      F S V (upd (upd W a (BitVec.ofNat 64 k)) b (BitVec.ofNat 64 G.D)) := R1.wq G' hb _
  have wb : InRegions u3.wr (F + BitVec.ofNat 64 (8 * b)) 8 := by
    rw [hwr3, hwr]; exact L.st (by unfold nW frameBytes at *; omega)
  refine WP.mono (Q := fun (u4 : State) => u4.mem = (u.mem.write (off F (8 * a)) 8 (BitVec.ofNat 64 k)).write
      (off F (8 * b)) 8 (BitVec.ofNat 64 G.D) ∧ u4.rd = u3.rd ∧ u4.wr = u3.wr ∧ u4.sp = u3.sp ∧ u4.v = u3.v ∧
      (∀ r ∈ preserved, r ≠ .x30 → u4.gpr r = u3.gpr r)) ?_ fun u4 ⟨hm4, hrd4, hwr4, hsp4, hv4, hcs4⟩ => ?_
  · have hsp3' : u3.sp = F := hsp3.trans (hsp.trans L.sp)
    oaep_run [hsp3', x10, wb, hb8.1, hb8.2, hm3, hm, BitVec.add_zero]
    oaep_fin
  have R' : Rep u4.mem F S V (upd (upd W a (BitVec.ofNat 64 k)) b (BitVec.ofNat 64 G.D)) := hm4 ▸ R2
  refine ⟨L.congr (hsp4.trans (hsp3.trans hsp)) (hwr4.trans (hwr3.trans hwr)) ?_,
    S1.trans ⟨hrd4.trans hrd3, hwr4.trans hwr3, hsp4.trans hsp3, fun r hr h30 => (hcs4 r hr h30).trans
      (hcs3 r hr h30), fun r _ => by rw [hv4, hv3], ?_⟩, R'⟩
  · rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide), upd, upd, ifn (Ne.symm hb12),
      ifn (Ne.symm ha12)]
  · rw [hm4, hm]
    exact Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _ (cF F (by unfold nW frameBytes at *; omega))

/-- `x11` all ones iff `k < 2 hLen + 2`, with `hLen` in its slot. -/
theorem chkK_ok {u : State} {F S : Addr} (Ly : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {D k : Nat} (hk : W 21 = BitVec.ofNat 64 k) (hl : W 4 = BitVec.ofNat 64 D)
    (hk' : k ≤ 1024) (hD : D ≤ 64) :
    WP isa (.block chkK) u fun u' => Lay u' F S ∧ Step F S [] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .x11 = if 2 * D + 2 ≤ k then 0 else BitVec.allOnes 64 := by
  have h168 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 168) 8 := Ly.ld (d := 168) (by decide)
  have h32 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 32) 8 := Ly.ld (d := 32) (by decide)
  have rk := R.rdK hk
  have rl := R.rd8 (d := 32) (k := 4) rfl (by decide) hl
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧
      u'.gpr .x11 = if 2 * D + 2 ≤ k then 0 else BitVec.allOnes 64) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x11⟩ =>
      ⟨Ly.congr hsp hwr (by rw [hm]), Step.blk _ hrd hwr hsp hv hcs hm, hm, x11⟩
  oaep_run [chkK, sK, sHl, h168, h32, Ly.sp, rk, rl, sbc_self, BitVec.ofNat_add_ofNat,
    show D + D + 2 = 2 * D + 2 by omega]
  refine ⟨trivial, trivial, trivial, trivial, trivial, cs_rfl, ?_⟩
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 2 * D + 2 < 2 ^ 64 by omega)]

/-! ## In constant time -/

/-- Code that keeps `sp`, constant time from states with the same `sp`. -/
theorem RelCT.keep_sp {P : State → State → Prop} {c : Prog isa} (h : RelCT isa P c fun _ _ => True)
    (hw : ∀ s, WP isa c s fun u => u.sp = s.sp) (hp : ∀ a b, P a b → a.sp = b.sp) :
    RelCT isa P c fun a b => a.sp = b.sp :=
  (h.wpDep (F := fun (s u : State) => u.sp = s.sp) fun a b _ => ⟨hw a, hw b⟩).mono (fun _ _ h => h)
    fun _ _ ⟨_, σ₁, σ₂, hσ, e₁, e₂⟩ => by rw [e₁, e₂]; exact hp _ _ hσ

/-- The number and its length to their slots, from two runs with the same
`sp` in which our stack argument `j` holds the same number `k`, in the
same time. The blocks are checked by the taint analysis (`ht₁`, `ht₃`). -/
theorem selArg_tr {hs : List Hash} {k : Nat} {G : Hash} (hn : Num hs k G) {j sel len : Nat}
    {h₁ h₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs []) (.block [.ldrSp .x16 (arg j), .addSp .x9 0, .str .x .x16 .x9 sel])
      h₁).isSome = true)
    (ht₃ : (taint.check (Taint.ofRegs []) (.block [.addSp .x9 0, .str .x .x10 .x9 len]) h₃).isSome = true)
    {P : State → State → Prop} (hp : ∀ a b, P a b → a.sp = b.sp)
    (hw : ∀ a b, P a b → ∀ s ∈ [a, b], WP isa (.block [.ldrSp .x16 (arg j), .addSp .x9 0, .str .x .x16 .x9 sel]) s
      fun u => u.sp = s.sp ∧ u.gpr .x16 = BitVec.ofNat 64 k) :
    RelCT isa P (selArg hs j sel len) fun _ _ => True := by
  have hk : k < 2 ^ 64 := by have := hn.k7; omega
  unfold selArg seqs seqs
  refine RelCT.seq (R := fun (a b : State) => a.sp = b.sp ∧ a.gpr .x16 = BitVec.ofNat 64 k ∧ b.gpr .x16 = BitVec.ofNat 64 k)
    (((RelCT.taint (A := taint) (P := P) (Taint.ofRegs []) (fun a b h =>
      ⟨hp a b h, fun _ hr => absurd (Taint.mem_ofRegs.mp hr) List.not_mem_nil⟩) ht₁).wpDep
      (F := fun (s u : State) => u.sp = s.sp ∧ u.gpr .x16 = BitVec.ofNat 64 k) fun a b h =>
        ⟨hw a b h a List.mem_cons_self, hw a b h b (List.mem_cons_of_mem _ List.mem_cons_self)⟩).mono
      (fun _ _ h => h) fun _ _ ⟨_, σ₁, σ₂, hσ, ⟨s₁, x₁⟩, ⟨s₂, x₂⟩⟩ => ⟨by rw [s₁, s₂]; exact hp _ _ hσ, x₁, x₂⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => a.sp = b.sp) (Proof.Dispatch.chain_relCT
    (Proof.Dispatch.AArch64.tests .x17 .x16 (by decide)) (cases_lt hn.len _) (by rw [cases_keys hn.len]; decide)
    (fun s₁ s₂ ⟨_, a16, b16⟩ => ?_) fun k' c hc => ?_) ?_
  · have e₁ : Proof.Dispatch.AArch64.sel .x16 s₁ = k := by
      show (s₁.gpr .x16).toNat = k; rw [a16, BitVec.toNat_ofNat]; omega
    have e₂ : Proof.Dispatch.AArch64.sel .x16 s₂ = k := by
      show (s₂.gpr .x16).toNat = k; rw [b16, BitVec.toNat_ofNat]; omega
    exact ⟨e₁.trans e₂.symm, e₁ ▸ cases_key hn _⟩
  · obtain ⟨h', hh', rfl⟩ : ∃ h', h' ∈ hs ∧ c = .block [.movz .x .x10 (BitVec.ofNat 16 h'.D) 0] := by
      obtain ⟨hl, -⟩ := hn
      match hs, hl with
      | [_, _, _, _, _, _, _, _], _ =>
        simp only [cases, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hc
        rcases hc with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
          exact ⟨_, by simp, rfl⟩
    refine RelCT.keep_sp (RelCT.taint (A := taint) (Taint.ofRegs []) (fun a b ⟨a₁, a₂, ⟨hsp, _⟩, _, ⟨v₁, e₁⟩,
      ⟨v₂, e₂⟩, _, _⟩ => ⟨by rw [e₁, e₂]; exact hsp, fun _ hr => absurd (Taint.mem_ofRegs.mp hr) List.not_mem_nil⟩)
      (check_of_zImm (τ := Taint.ofRegs []) (c := .block [.movz .x .x10 (BitVec.ofNat 16 h'.D) 0])
        (c' := .block [.movz .x .x10 0 0]) rfl (by taint_decide)))
      (fun s => ?_) fun a b ⟨a₁, a₂, ⟨hsp, _⟩, _, ⟨v₁, e₁⟩, ⟨v₂, e₂⟩, _, _⟩ => by rw [e₁, e₂]; exact hsp
    oaep_run []
  · exact RelCT.taint (A := taint) (Taint.ofRegs []) (fun a b h =>
      ⟨h, fun _ hr => absurd (Taint.mem_ofRegs.mp hr) List.not_mem_nil⟩) ht₃

end VG.Proof.RsaOaep.AArch64
