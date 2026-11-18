module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCorrect
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
public import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
public import VerifiedGarbage.Proof.RsaPss.X86_64.PrefixCheck
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFrame
import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignPro
import VerifiedGarbage.Proof.RsaPss.X86_64.FixedHash
import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.RsaPss.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaPss.X86_64.SignEnc
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
import VerifiedGarbage.Proof.RsaPss.X86_64.Params
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.RsaPss.X86_64.TabCall

/-! ### `RsaPss.X86_64.VerifyMain`, which this module and modules that import it used -/

section

/-! ### `RsaPss.X86_64.VerifyCall`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS verification on x86-64: the call of `vg_rsa_public_checked`

Its stack arguments (`vArg`), in the frame's first 4 words: the signature,
`k`, the rest of `scratch` (`vstackArg_call`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (pubChkContract)

variable {tsH tsG : List FnTable}

/-- Its stack arguments. -/
def vArg (s : State) (i : Nat) : BitVec 64 :=
  match i with
  | 0 => stackArg s 0
  | 1 => s.gpr .rsi
  | 2 => off (stackArg s 4) oRsa
  | _ => stackArg s 5 - BitVec.ofNat 64 1024

theorem vfb_sub8 {s : State} (hp : VPre tsH tsG s) : (fb s - 8).toNat = (fb s).toNat - 8 := by
  have hF := vfb_toNat hp; have := hp.sp1
  rw [BitVec.toNat_sub]; unfold verifyStack frameBytes at *
  rw [show (8 : BitVec 64).toNat = 8 from rfl]; omega_arith

theorem vstackArg_call {s t : State} (hp : VPre tsH tsG s) (hsp : t.gpr .rsp = fb s) (rd wr : List Region) {i : Nat}
    (hi : i < 4) : stackArg (t.callEntry.withRegions rd wr) i = word t.mem (fb s) (8 * i) := by
  have hF := vfb_toNat hp
  have := hp.sp1; have := hp.sp2
  have hsep := Offset.sep (fb s - 8) (d := 8 * (i + 1)) (n := 8) (e := 0) (k := 8) (by omega_arith) (by omega_arith)
    (by unfold verifyStack frameBytes at *; omega_arith)
  rw [show fb s - 8 + BitVec.ofNat 64 0 = fb s - 8 from BitVec.add_zero _] at hsep
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp]
  rw [Mem.readW_writeW_sep hsep (by decide)]
  show _ = t.mem.readW (off (fb s) (8 * i)) 64
  have ea : fb s - 8 + BitVec.ofNat 64 (8 * (i + 1)) = off (fb s) (8 * i) := by
    simp only [off]
    rw [show 8 * (i + 1) = 8 + 8 * i by omega_arith, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
      show BitVec.ofNat 64 8 = 8 from rfl, BitVec.sub_add_cancel]
  rw [ea]

theorem vsc_sub {s : State} (hp : VPre tsH tsG s) :
    (stackArg s 5 - 1024#64).toNat = (stackArg s 5).toNat - 1024 := by
  have := hp.hsl; have := hp.k1
  rw [BitVec.toNat_sub, show (1024#64).toNat = 1024 from rfl]; omega_arith

end VG.Proof.RsaPss.X86_64

end

end

/-!
# RSASSA-PSS verification on x86-64: after the checks

`vfront_ok`: `DB`'s slots, the public-key operation's arguments, and the
call, which leaves RSAVP1's result (zeros if it fails, `vx`) at
`scratch + oEm`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (pubChkContract)

variable {tsH tsG : List FnTable}

theorem WP.seq_inv {A B : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq A B) s Q) :
    WP isa A s fun t => WP isa B t Q := by
  obtain ⟨t, s', he, hq⟩ := h
  cases he with | seq h1 h2 => exact ⟨_, _, h1, _, _, h2, hq⟩

/-- A sequence, in two pieces. -/
theorem WP.seqs_append : ∀ {l₁ l₂ : List (Prog isa)}, l₁ ≠ [] → l₂ ≠ [] → ∀ {s : State} {Q : State → Prop},
    WP isa (seqs l₁) s (fun t => WP isa (seqs l₂) t Q) → WP isa (seqs (l₁ ++ l₂)) s Q
  | [], _, h₁, _, _, _, _ => absurd rfl h₁
  | [c], l₂, _, h₂, s, Q, h => by
    obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil h₂
    exact WP.seq h
  | c :: c' :: cs, l₂, _, h₂, s, Q, h => by
    obtain ih := @WP.seqs_append (c' :: cs) l₂ (List.cons_ne_nil _ _) h₂
    exact WP.seq (WP.mono (WP.seq_inv h) fun t ht => ih ht)

theorem vframe_keep {s u v : State} (hp : VPre tsH tsG s) (hw : u.wr = frR s :: s.wr) (hsp : u.gpr .rsp = fb s)
    (hM : Frame (vwrR s) s.mem u.mem)
    (hk : ∀ a, (∀ r ∈ u.wr, ¬ r.Contains a 1) → ¬ (below (u.gpr .rsp) 16).Contains a 1 → v.mem a = u.mem a) :
    Frame (vwrR s) s.mem v.mem := by
  intro x hx
  refine (hk x (fun r hr hc => ?_) (fun hc => ?_)).trans (hM x hx)
  · rw [hw, hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hx _ (List.mem_cons_self ..) (vframe_sub s x hc)
    · exact hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hc
  · rw [hsp] at hc; exact hx _ (List.mem_cons_self ..) (vret_sub s x hc)

/-! ## `DB`, its first nonzero byte, and `acc` -/

theorem fnz_congr {f g : Nat → Byte} : ∀ {j : Nat}, (∀ i < j, f i = g i) → fnz f j = fnz g j
  | 0, _ => rfl
  | j + 1, h => by
    simp only [fnz, fnz_congr (j := j) (fun i hi => h i (by omega_arith)), h j (by omega_arith)]

/-- `DB` after the mask and the top bits. -/
theorem db_bytes (V : Nat → Byte) (mk : List Byte) {e db z : Nat} (hmk : mk.length = db) :
    ∀ i < db, upd (mixV V mk e db) e (mixV V mk e db e &&& ((0xFF : Byte) >>> z)) (e + i) =
      (Spec.RsaPss.clearTop z (Spec.Mgf1.xorBytes ((List.range db).map fun i => V (e + i)) mk)).getD i 0 := by
  intro i hi
  rw [clearTop_getD]
  obtain hx : ∀ j < db, (Spec.Mgf1.xorBytes ((List.range db).map fun i => V (e + i)) mk).getD j 0 =
      V (e + j) ^^^ mk.getD j 0 := fun j hj => by
    rw [xorBytes_getD (by simp; omega_arith) (by omega_arith), getD_map_range, ifp hj]
  simp only [upd, mixV]
  by_cases h0 : i = 0
  · subst h0
    rw [ifp (by omega_arith), ifp rfl, ifp (show e ≤ e ∧ e < e + db by omega_arith), hx 0 hi, Nat.sub_self, Nat.add_zero]
  · rw [ifn (by omega_arith), ifn h0, ifp (show e ≤ e + i ∧ e + i < e + db by omega_arith), hx i hi,
      show e + i - e = i by omega_arith]

variable {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : Pbkdf2.Md.X86_64.HashOK H) (K : Pbkdf2.Md.X86_64.Callees H)

include hH in
/-- `scanCheck`: `acc` and the slots of `pos` and `ℓ`, by `prefixCheck` when the
salt's length is given and less than `db` (`ff`), by `posScan` and `posCheck`
otherwise. -/
theorem vscan_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db : Nat} {fixed : Bool} {dbL : List Byte}
    (he : W 23 = off S e) (hdb : W 24 = BitVec.ofNat 64 db) (hany : W 35 = if fixed then 0 else 1)
    (hdb1 : 1 ≤ db) (hfit : e + db ≤ oRsa) (hdb2 : db ≤ 1024)
    (hV : ∀ i < db, V (e + i) = dbL.getD i 0) (hlen : dbL.length = db) :
    let ff := fixed && decide ((W 36).toNat < db)
    let fd := decide (lz dbL < db)
    let pos := if ff then db - (W 36).toNat - 1 else if lz dbL < db then lz dbL else 0
    let val := if lz dbL < db then dbL.getD (lz dbL) 0 else 0
    WP isa (scanCheck H) u fun u' => Lay u' F S ∧
      Keep [.rdi, .r10, .r8, .rdx, .rsi, .r11, .rax, .r9, .rcx] u u' ∧
      ∃ a, (a = 0 ↔ W 33 = 0 ∧ (if ff then (∀ i < pos, dbL.getD i 0 = 0) ∧ dbL.getD pos 0 = 1
          else val = 1 ∧ fd = true ∧ (fixed = true → BitVec.ofNat 64 (db - pos - 1) = W 36))) ∧
        Rep u'.mem F S V (upd (upd (upd W 34 (BitVec.ofNat 64 pos)) 33 a) 27
          (BitVec.ofNat 64 (db - pos - 1 + (8 + H.D)))) := by
  intro ff fd pos val
  obtain hfnz : fnz (fun i => V (e + i)) db = if lz dbL < db then some (lz dbL) else none := by
    rw [fnz_congr (g := fun i => dbL.getD i 0) fun i hi => hV i hi]
    exact fnz_lz dbL db (by omega_arith)
  obtain generic : ∀ v : State, Keep [.rax] u v → v.mem = u.mem → ff = false →
      WP isa (.seq posScan (posCheck H)) v fun u' => Lay u' F S ∧
        Keep [.rdi, .r10, .r8, .rdx, .rsi, .r11, .rax, .r9, .rcx] u u' ∧
        ∃ a, (a = 0 ↔ W 33 = 0 ∧ (if ff then (∀ i < pos, dbL.getD i 0 = 0) ∧ dbL.getD pos 0 = 1
            else val = 1 ∧ fd = true ∧ (fixed = true → BitVec.ofNat 64 (db - pos - 1) = W 36))) ∧
          Rep u'.mem F S V (upd (upd (upd W 34 (BitVec.ofNat 64 pos)) 33 a) 27
            (BitVec.ofNat 64 (db - pos - 1 + (8 + H.D)))) := by
    intro v kv hm hff
    obtain Lv := L.congr (kv.gpr (by decide)) kv.2.2 (by rw [hm])
    obtain Rv : Rep v.mem F S V W := hm ▸ R
    obtain hpos' : pos = if lz dbL < db then lz dbL else 0 := by simp only [pos, hff, Bool.false_eq_true, ite_false]
    refine WP.seq (WP.mono (posScan_ok Lv Rv he hdb hdb1 hfit) fun v4 ⟨k4, hm4, hdx4, hsi4, h114⟩ => ?_)
    rw [hfnz] at hdx4 hsi4 h114
    obtain L4 := Lv.congr (k4.gpr (by decide)) k4.2.2 (by rw [hm4])
    obtain R4 : Rep v4.mem F S V W := hm4 ▸ Rv
    obtain hp : pos < db := by rw [hpos']; split <;> omega_arith
    refine WP.mono (posCheck_ok hH L4 R4 (db := db) (pos := pos) (fd := fd) (val := val) hdb hany hp
      (by rw [hdx4]; simp only [fd]; by_cases hc : lz dbL < db <;> simp [hc])
      (by rw [hsi4, hpos']; by_cases hc : lz dbL < db <;> simp [hc])
      (by rw [h114]; simp only [val]; by_cases hc : lz dbL < db <;> [simp [hc, hV _ hc]; simp [hc]]))
      fun v5 ⟨L5, k5, R5⟩ => ⟨L5, ((kv.trans k4).trans k5).mono (by decide), _, ?_, R5⟩
    rw [acc1V_eq_zero, hff]
    simp only [Bool.false_eq_true, ite_false]
  unfold scanCheck
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun v =>
    v.mem = u.mem ∧ v.zf = some (decide (W 35 = 0))) ?_ rfl) fun v ⟨⟨hm, hz⟩, kv⟩ => ?_)
  · xrun [ea_sp, L.rsp, L.ld (d := sAny) (by decide), R.rd (d := sAny) 35 rfl (by decide)]
    rw [BitVec.and_self]
    rfl
  obtain Lv := L.congr (kv.gpr (by decide)) kv.2.2 (by rw [hm])
  obtain Rv : Rep v.mem F S V W := hm ▸ R
  refine WP.ite (M := isa) _ (show isa.eval .e v = _ from hz) (fun hb => ?_) (fun hb => ?_)
  · rw [decide_eq_true_eq, hany] at hb
    obtain hfx : fixed = true := by cases fixed <;> simp_all
    refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun w =>
      w.mem = v.mem ∧ w.cf = some (decide ((W 36).toNat < db))) ?_ rfl) fun w ⟨⟨hmw, hc⟩, kw⟩ => ?_)
    · xrun [ea_sp, Lv.rsp, Lv.ld (d := sSlen) (by decide), Lv.ld (d := sDb) (by decide),
        Rv.rd (d := sSlen) 36 rfl (by decide), Rv.rd (d := sDb) 24 rfl (by decide), hdb]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show db < 2 ^ 64 by omega_arith)]
    obtain kuw : Keep [.rax] u w := (kv.trans kw).mono (by decide)
    obtain hmu : w.mem = u.mem := hmw.trans hm
    refine WP.ite (M := isa) _ (show isa.eval .b w = _ from hc) (fun hf => ?_) (fun hf => ?_)
    · rw [decide_eq_true_eq] at hf
      obtain hff : ff = true := by simp only [ff, hfx, hf, decide_true, Bool.and_self]
      obtain hp : pos = db - (W 36).toNat - 1 := by simp only [pos, hff, ite_true]
      obtain Lw := L.congr (kuw.gpr (by decide)) kuw.2.2 (by rw [hmu])
      refine WP.mono (prefixCheck_ok hH Lw (hmu ▸ R) he hdb (show W 36 = BitVec.ofNat 64 (W 36).toNat by simp)
        hf hfit hdb2) fun u' ⟨L', k', a, ha, R'⟩ => ⟨L', (kuw.trans k').mono (by decide), a, ?_, ?_⟩
      · rw [ha, hff, hp]
        simp only [ite_true, ZeroUpTo]
        refine and_congr_right fun _ => and_congr (forall_congr' fun i => imp_congr_right fun hi => ?_) ?_
        · rw [hV i (by omega_arith)]
        · rw [hV _ (by omega_arith)]
      · rw [hp, show db - (db - (W 36).toNat - 1) - 1 + (8 + H.D) = (W 36).toNat + (8 + H.D) by omega_arith]
        exact R'
    · rw [decide_eq_false_iff_not] at hf
      exact generic w kuw hmu (by simp only [ff, hfx, hf, decide_false, Bool.and_false])
  · rw [decide_eq_false_iff_not, hany] at hb
    obtain hfx : fixed = false := by cases fixed <;> simp_all
    exact generic v kv hm (by simp only [ff, hfx, Bool.false_and])

include hH in
theorem vmid_ok {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Pbkdf2.Md.X86_64.Calls.StreamOK G) {Gs : Spec.Mgf1.Hash}
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
    {g : Impl.Mgf1.X86_64.Table.Fns} {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem F S V W) (hGT : GT G g W u.syms) {k lo db z : Nat} {fixed : Bool}
    (hk : W 17 = BitVec.ofNat 64 k) (he : W 23 = off S (oEm + lo)) (hdb : W 24 = BitVec.ofNat 64 db)
    (hc : W 25 = BitVec.setWidth 64 ((0xFF : Byte) >>> z)) (hlo : W 26 = BitVec.ofNat 64 lo)
    (hany : W 35 = if fixed then 0 else 1)
    (hlo1 : lo ≤ 1) (hdb1 : 1 ≤ db) (hlay : lo + db + H.D + 1 = k) (hk2 : k ≤ 1024) :
    let hB := (List.range H.D).map fun i => V (oEm + lo + db + i)
    let dbL := Spec.RsaPss.clearTop z (Spec.Mgf1.xorBytes ((List.range db).map fun i => V (oEm + lo + i))
      (Spec.Mgf1.mgf1 Gs hB db))
    let ff := fixed && decide ((W 36).toNat < db)
    let fd := decide (lz dbL < db)
    let pos := if ff then db - (W 36).toNat - 1 else if lz dbL < db then lz dbL else 0
    let val := if lz dbL < db then dbL.getD (lz dbL) 0 else 0
    WP isa (seqs [.block acc0, mgfXor H g, .block clearTop, scanCheck H]) u fun u' => Lay u' F S ∧
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], u'.gpr r = u.gpr r) ∧
      ∃ V' W', Rep u'.mem F S V' W' ∧
        (W' 33 = 0 ↔ acc0V (V (oEm + k - 1)) (V oEm) (V (oEm + lo)) ((0xFF : Byte) >>> z) lo = 0 ∧
          (if ff then (∀ i < pos, dbL.getD i 0 = 0) ∧ dbL.getD pos 0 = 1
          else val = 1 ∧ fd = true ∧ (fixed = true → BitVec.ofNat 64 (db - pos - 1) = W 36))) ∧
        W' 34 = BitVec.ofNat 64 pos ∧ W' 27 = BitVec.ofNat 64 (db - pos - 1 + (8 + H.D)) ∧
        (∀ j < nW, (j < 27 ∨ 34 < j) → W' j = W j) ∧
        (∀ i < db, V' (oEm + lo + i) = dbL.getD i 0) ∧
        (∀ o < oRsa, ctOut o → ¬ (oEm + lo ≤ o ∧ o < oEm + lo + db) → V' o = V o) := by
  intro hB dbL ff fd pos val
  have hD := hH.hD0
  have hDN := hH.hDN
  have c1 : oEm = 2560 := rfl
  have c5 : oRsa = 8192 := rfl
  simp only [seqs]
  -- `acc0`.
  refine WP.seq (X86_64.WP.mono_syms (acc0_ok L R (c := (0xFF : Byte) >>> z) hk he hc hlo (by omega_arith) hk2
    (by omega_arith)) fun u1 ⟨L1, k1, R1⟩ sy1 => ?_)
  set a0 := acc0V (V (oEm + k - 1)) (V oEm) (V (oEm + lo)) ((0xFF : Byte) >>> z) lo
  obtain g1 : ∀ j, j ≠ 33 → upd W 33 a0 j = W j := fun j h => by simp [upd, h]
  -- The mask.
  refine WP.seq (WP.mono (mgfXor_ok hG hGh hGl hGv H L1 R1
    (hGT.congr sy1 fun j h1 h2 => g1 j (by omega_arith)) (e := oEm + lo) (db := db)
    ⟨by omega_arith, hdb1, by omega_arith⟩ (by rw [g1 23 (by decide), he]) (by rw [g1 24 (by decide), hdb]))
    fun u2 ⟨L2, rd2, wr2, cs2, V2, W2, R2, hW2, hV2⟩ => ?_)
  -- The top bits.
  obtain h23 : W2 23 = off S (oEm + lo) := by rw [hW2 23 (by decide) (by omega_arith), g1 23 (by decide), he]
  obtain h25 : W2 25 = BitVec.setWidth 64 ((0xFF : Byte) >>> z) := by
    rw [hW2 25 (by decide) (by omega_arith), g1 25 (by decide), hc]
  refine WP.seq (WP.mono (clearTop_ok L2 R2 (e := oEm + lo) h23 h25 (by omega_arith)) fun u3 ⟨L3, k3, R3⟩ => ?_)
  set V3 := upd V2 (oEm + lo) (V2 (oEm + lo) &&& ((0xFF : Byte) >>> z))
  -- `DB`'s bytes.
  obtain hmk : (Spec.Mgf1.mgf1 Gs hB db).length = db := Proof.Mgf1.mgf1_length hGv _ _
  obtain hV3 : ∀ i < db, V3 (oEm + lo + i) = dbL.getD i 0 := fun i hi => by
    have hm : ∀ o < oRsa, ctOut o → V2 o = mixV V (Spec.Mgf1.mgf1 Gs hB db) (oEm + lo) db o := hV2
    obtain hco : ∀ j < db, ctOut (oEm + lo + j) := fun j hj => ⟨by unfold oLen; omega_arith, by unfold oY; omega_arith⟩
    have := db_bytes V (Spec.Mgf1.mgf1 Gs hB db) (e := oEm + lo) (z := z) hmk i hi
    rw [← this]
    simp only [V3, upd]
    by_cases h0 : i = 0
    · subst h0
      obtain hco0 : ctOut (oEm + lo) := ⟨by unfold oLen; omega_arith, by unfold oY; omega_arith⟩
      rw [Nat.add_zero, ifp rfl, ifp rfl, hm _ (by omega_arith) hco0]
    · rw [ifn (by omega_arith), ifn (by omega_arith), hm _ (by omega_arith) (hco i hi)]
  have R3' : Rep u3.mem F S V3 W2 := R3
  have h23' : W2 23 = off S (oEm + lo) := h23
  obtain h24 : W2 24 = BitVec.ofNat 64 db := by rw [hW2 24 (by decide) (by omega_arith), g1 24 (by decide), hdb]
  obtain h35 : W2 35 = if fixed then 0 else 1 := by rw [hW2 35 (by decide) (by omega_arith), g1 35 (by decide), hany]
  obtain h36 : W2 36 = W 36 := by rw [hW2 36 (by decide) (by omega_arith), g1 36 (by decide)]
  obtain h33 : W2 33 = acc0V (V (oEm + k - 1)) (V oEm) (V (oEm + lo)) ((0xFF : Byte) >>> z) lo := by
    rw [hW2 33 (by decide) (by omega_arith)]; simp [upd]; rfl
  obtain hlen : dbL.length = db := by simp only [dbL]; rw [clearTop_length, Proof.Mgf1.xorBytes_length]; simp [hmk]
  -- The padding's checks.
  obtain hscan := vscan_ok hH L3 R3' (e := oEm + lo) (db := db) (fixed := fixed) (dbL := dbL) h23' h24 h35 hdb1
    (by omega_arith) (by omega_arith) hV3 hlen
  rw [h36] at hscan
  refine WP.mono hscan fun u5 ⟨L5, k5, a, ha, R5⟩ => ?_
  refine ⟨L5, ?_, ?_, fun r hr => ?_, _, _, R5, ?_, by simp only [upd, Nat.reduceEqDiff, ite_true, ite_false]; rfl,
    by simp only [upd, Nat.reduceEqDiff, ite_true, ite_false]; rfl, fun j hj hj' => ?_, fun i hi => ?_,
    fun o ho hco hn => ?_⟩
  · rw [k5.2.1, k3.2.1, rd2, k1.2.1]
  · rw [k5.2.2, k3.2.2, wr2, k1.2.2]
  · rw [keep_cs k5 (by decide) r hr, keep_cs k3 (by decide) r hr, cs2 r hr, keep_cs k1 (by decide) r hr]
  · simp only [upd, Nat.reduceEqDiff, ite_true, ite_false]
    rw [ha, h33]
  · simp only [upd]
    rw [ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), hW2 j hj (by omega_arith), g1 j (by omega_arith)]
  · exact hV3 i hi
  · simp only [V3, upd]
    rw [ifn (by omega_arith), hV2 o ho hco]
    simp only [mixV]
    rw [ifn hn]

/-! ## The salt, its hash, and the result -/

include hH K in
theorem vback_ok (lk : Pbkdf2.Md.X86_64.MgfLink H hH) {dn : String} {f : MdFns} (hdk : DigOK H)
    {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem F S V W) (hT : HT H dn f W u.syms) {lo db pos : Nat} {dig : Addr}
    (he : W 23 = off S (oEm + lo)) (hdb : W 24 = BitVec.ofNat 64 db) (hpos : W 34 = BitVec.ofNat 64 pos)
    (hl : W 27 = BitVec.ofNat 64 (db - pos - 1 + (8 + H.D))) (hdg : W 37 = dig)
    (hlo1 : lo ≤ 1) (hdb1 : 1 ≤ db) (hpd : pos < db) (hfit : lo + db + H.D + 1 ≤ 1024)
    (hdR : ∀ i < H.D, InRegions (u.rd ++ u.wr) (dig + BitVec.ofNat 64 i) 1)
    (hdO : ∀ i < H.D, Outside u.wr F (dig + BitVec.ofNat 64 i)) :
    let msg := Spec.RsaPss.zeros 8 ++ (List.range H.D).map (bytesF u.mem dig) ++
      ((List.range db).map fun i => V (oEm + lo + i)).drop (pos + 1)
    WP isa (seqs [clearY, copyDigest H, copyDb H, shift H, .block (verifyNb H), ctHash f H, cmpH H]) u fun u' =>
      Lay u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], u'.gpr r = u.gpr r) ∧
      (∃ V' W', Rep u'.mem F S V' W' ∧
        ∀ j < nW, j ≠ 28 → j ≠ 29 → j ≠ 30 → j ≠ 44 → j ≠ 45 → j ≠ 46 → W' j = W j) ∧
      u'.gpr .rax = if W 33 = 0 ∧ ∀ i < H.D, (lk.G.hash msg).getD i 0 = V (oEm + lo + db + i) then 1 else 0 := by
  intro msg
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c3 : oDig = 2304 := rfl
  have c5 : oRsa = 8192 := rfl
  simp only [seqs]
  -- `Y` cleared.
  refine WP.seq (X86_64.WP.mono_syms (WP.keepIn (by safe_by [clearY]) (by exact Nat.zero_le 16)
    (clearY_ok L R)) fun u1 ⟨⟨L1, k1, hcx1, R1⟩, f1⟩ sy1 => ?_)
  obtain hS1 := chain (u := u) rfl L.rsp (fun _ _ => rfl) f1
  -- `mHash`.
  refine WP.seq (X86_64.WP.mono_syms (WP.keepIn (by safe_by [copyDigest]) (by exact Nat.zero_le 16)
    (copyDigest_ok hH L1 R1 (p := dig) hdg hcx1
      (fun i hi => by rw [k1.2.1, k1.2.2]; exact hdR i hi)
      (fun i hi j hj => Outside.ne L1 (by rw [k1.2.2]; exact hdO i hi) (by omega_arith))))
    fun u2 ⟨⟨L2, k2, R2⟩, f2⟩ sy2 => ?_)
  obtain hS2 := chain (u := u) k1.2.2 L1.rsp hS1 f2
  -- `DB`.
  refine WP.seq (X86_64.WP.mono_syms (copyDb_ok L2 R2 (e := oEm + lo) (db := db) he hdb
    ((k2.gpr (by decide)).trans hcx1) hdb1 (by omega_arith) (by omega_arith)) fun u3 ⟨L3, k3, R3⟩ sy3 => ?_)
  set V4 := clrV V oY 2048 with hV4
  set V5 := cpV V4 (fun i => u1.mem (dig + BitVec.ofNat 64 i)) (oY + 8) H.D with hV5
  set V6 := cpV V5 (fun i => V5 (oEm + lo + i)) (oY + (8 + H.D)) db with hV6
  obtain e5 : ∀ i < db, V5 (oEm + lo + i) = V (oEm + lo + i) := fun i hi => by
    simp only [hV5, hV4, cpV, clrV]; rw [ifn (by omega_arith), ifn (by omega_arith)]
  -- The shift.
  obtain hz : ∀ j, db ≤ j → j < db + 512 → V6 (oY + 8 + H.D + j) = 0 := fun j h1 h2 => by
    simp only [hV6, hV5, hV4, cpV, clrV]; rw [ifn (by omega_arith), ifn (by omega_arith), ifp (by omega_arith)]
  refine WP.seq (X86_64.WP.mono_syms (shift_ok hH L3 R3 (pos := pos) (db := db) hpos hdb (by omega_arith) hdb1
    (by omega_arith) hz) fun u4 I4 sy4 => ?_)
  obtain ⟨V7, W4, R4, -, -, -, hW4, hV7, hO7⟩ := I4.rep
  obtain hp10 : (pos + 1) % 2 ^ 10 = pos + 1 := Nat.mod_eq_of_lt (by rw [show (2 : Nat) ^ 10 = 1024 from rfl]; omega_arith)
  rw [hp10] at hV7
  obtain g4 : ∀ j, j ≠ 44 → j ≠ 45 → j ≠ 46 → j < nW → W4 j = W j := fun j a b c d => hW4 j d a b c
  -- `nbm`.
  refine WP.seq (X86_64.WP.mono_syms (verifyNb_ok hH I4.L R4 (db := db) (by rw [g4 24 (by decide) (by decide)
    (by decide) (by decide), hdb]) (by omega_arith)) fun u5 ⟨L5, k5, R5⟩ sy5 => ?_)
  -- The hash of `M'`.
  obtain hml : msg.length = db - pos - 1 + (8 + H.D) := by
    simp only [msg, List.length_append, RsaPss.zeros_length, List.length_map, List.length_range, List.length_drop]
    omega_arith
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hL := hH.dims.L
  obtain hnb1 := Nat.lt_div_mul_add (a := db + (7 + H.D + H.P.L)) (b := H.P.B) hB0
  obtain hnb2 := Nat.div_mul_le_self (db + (7 + H.D + H.P.L)) H.P.B
  obtain hmsg : ∀ i, msg.getD i 0 = if i < 8 then 0 else if i < 8 + H.D then u.mem (dig + BitVec.ofNat 64 (i - 8))
      else if i < 8 + H.D + (db - (pos + 1)) then V (oEm + lo + (pos + 1 + (i - (8 + H.D)))) else 0 := fun i => by
    simp only [msg, getD_app, List.length_append, RsaPss.zeros_length, List.length_map, List.length_range,
      getD_map_range, bytesF, RsaPss.zeros_getD]
    by_cases h1 : i < 8
    · rw [ifp (by omega_arith), ifp h1, ifp h1]
    by_cases h2 : i < 8 + H.D
    · rw [ifp h2, ifn h1, ifp (by omega_arith), ifn h1, ifp h2]
    rw [ifn h2, ifn h1, ifn h2]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_map]
    by_cases h3 : i < 8 + H.D + (db - (pos + 1))
    · rw [ifp h3, List.getElem?_range (by omega_arith)]; rfl
    · rw [ifn h3, List.getElem?_eq_none (by simp; omega_arith)]; rfl
  refine WP.seq (WP.mono (ctHash_ok hH K L5 R5 (msg := msg) (nbm := (db + (7 + H.D + H.P.L)) / H.P.B + 1)
      (by rw [hml]; simp only [upd]; rw [ifn (by decide), g4 27 (by decide) (by decide) (by decide) (by decide), hl])
      (by simp [upd]) (by rw [hml, Nat.succ_mul]; omega_arith) (by rw [Nat.succ_mul]; omega_arith) (fun i hi => ?_)
      (hT.congr (sy5.trans (sy4.trans (sy3.trans (sy2.trans sy1))))
        (by rw [upd_ne' (by decide), g4 8 (by decide) (by decide) (by decide) (by decide)])
        (by rw [upd_ne' (by decide), g4 9 (by decide) (by decide) (by decide) (by decide)])
        (by rw [upd_ne' (by decide), g4 10 (by decide) (by decide) (by decide) (by decide)])) hdk)
    fun u6 ⟨L6, rd6, wr6, cs6, V8, W6, R6, hout6, hW6, hdig6⟩ => ?_)
  · rw [hmsg]
    obtain hi' : i < 2048 := by rw [Nat.succ_mul] at hi; omega_arith
    by_cases hY : 8 + H.D ≤ i ∧ i < 8 + H.D + db
    · have := hV7 (i - (8 + H.D)) (by omega_arith)
      rw [show oY + 8 + H.D + (i - (8 + H.D)) = oY + i by omega_arith] at this
      rw [this, ifn (show ¬ i < 8 by omega_arith), ifn (show ¬ i < 8 + H.D by omega_arith)]
      by_cases h3 : i - (8 + H.D) + (pos + 1) < db
      · rw [ifp h3, ifp (show i < 8 + H.D + (db - (pos + 1)) by omega_arith)]
        simp only [hV6, cpV]
        rw [ifp (by omega_arith), show oY + 8 + H.D + (i - (8 + H.D) + (pos + 1)) - (oY + (8 + H.D)) =
          pos + 1 + (i - (8 + H.D)) by omega_arith, e5 _ (by omega_arith)]
      · rw [ifn h3, ifn (show ¬ i < 8 + H.D + (db - (pos + 1)) by omega_arith)]
    · rw [hO7 _ (by omega_arith)]
      simp only [hV6, hV5, hV4, cpV, clrV]
      rw [ifn (by omega_arith)]
      by_cases h1 : i < 8
      · rw [ifn (by omega_arith), ifp (by omega_arith), ifp h1]
      by_cases h2 : i < 8 + H.D
      · rw [ifp (by omega_arith), ifn h1, ifp h2, show oY + i - (oY + 8) = i - 8 by omega_arith]
        exact hS1 _ (hdO _ (by omega_arith))
      · rw [ifn (by omega_arith), ifp (by omega_arith), ifn h1, ifn h2, ifn (by omega_arith)]
  -- The comparison.
  obtain h23 : W6 23 = off S (oEm + lo) := by
    rw [hW6 23 (by decide) (by decide) (by decide)]; simp only [upd]
    rw [ifn (by decide), g4 23 (by decide) (by decide) (by decide) (by decide), he]
  obtain h24 : W6 24 = BitVec.ofNat 64 db := by
    rw [hW6 24 (by decide) (by decide) (by decide)]; simp only [upd]
    rw [ifn (by decide), g4 24 (by decide) (by decide) (by decide) (by decide), hdb]
  refine WP.mono (cmpH_ok hH L6 R6 h23 h24 (by omega_arith)) fun u7 ⟨k7, hm7, hax7⟩ => ?_
  obtain L7 : Lay u7 F S := L6.congr (k7.gpr (by decide)) k7.2.2 (by rw [hm7])
  obtain hrd : u6.rd = u.rd := by
    rw [rd6, k5.2.1, I4.keep.2.1, k3.2.1, k2.2.1, k1.2.1]
  obtain hwr : u6.wr = u.wr := by
    rw [wr6, k5.2.2, I4.keep.2.2, k3.2.2, k2.2.2, k1.2.2]
  refine ⟨L7, k7.2.1.trans hrd, k7.2.2.trans hwr, fun r hr => ?_, ⟨V8, W6, hm7 ▸ R6, fun j hj a b c d e f => ?_⟩, ?_⟩
  · rw [keep_cs k7 (by decide) r hr, cs6 r hr, keep_cs k5 (by decide) r hr, keep_cs I4.keep (by decide) r hr,
      keep_cs k3 (by decide) r hr, keep_cs k2 (by decide) r hr, keep_cs k1 (by decide) r hr]
  · rw [hW6 j hj b c]; simp only [upd]; rw [ifn a, g4 j d e f hj]
  · rw [hax7]
    obtain h33 : W6 33 = W 33 := by
      rw [hW6 33 (by decide) (by decide) (by decide)]; simp only [upd]
      rw [ifn (by decide), g4 33 (by decide) (by decide) (by decide) (by decide)]
    obtain hH' : ∀ i < H.D, V8 (oDig + i) = (lk.G.hash msg).getD i 0 := fun i hi => by
      rw [map_range_getD hdig6 hi, ← lk.hash]
    obtain hE : ∀ i < H.D, V8 (oEm + lo + db + i) = V (oEm + lo + db + i) := fun i hi => by
      rw [hout6 _ (by omega_arith) ⟨by unfold oLen; omega_arith, by omega_arith⟩, hO7 _ (by omega_arith)]
      simp only [hV6, hV5, hV4, cpV, clrV]
      rw [ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith)]
    rw [h33]
    congr 1
    apply propext
    exact and_congr_right fun _ => forall_congr' fun i => imp_congr_right fun hi => by rw [hH' i hi, hE i hi]

end VG.Proof.RsaPss.X86_64

end

end

/-! ### `RsaPss.X86_64.VerifyPadding`, which this module and modules that import it used -/

section

/-! ### `RsaPss.X86_64.SaltBack`, which this module and modules that import it used -/

section

/-! ### `RsaPss.X86_64.FixedSaltBack`, which only this module used -/

section

/-! Verification's fixed-length salt input, built without a masked shift. -/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)

variable {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : Pbkdf2.Md.X86_64.HashOK H)
  (K : Pbkdf2.Md.X86_64.Callees H)

include hH K in
theorem fixedSaltBack_ok (lk : Pbkdf2.Md.X86_64.MgfLink H hH)
    {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {lo db sl : Nat} {dig : Addr}
    (he : W 23 = off S (oEm + lo)) (hdb : W 24 = BitVec.ofNat 64 db)
    (hsl : W 36 = BitVec.ofNat 64 sl) (hdg : W 37 = dig)
    (hlo : lo ≤ 1) (hslFit : sl < db) (hfit : lo + db + H.D + 1 ≤ 1024)
    (hdR : ∀ i < H.D, InRegions (u.rd ++ u.wr) (dig + BitVec.ofNat 64 i) 1)
    (hdO : ∀ i < H.D, Outside u.wr F (dig + BitVec.ofNat 64 i)) {dn : String} {f : MdFns}
    (hT : HT H dn f W u.syms) (hdk : DigOK H) :
    let msg := Spec.RsaPss.zeros 8 ++ (List.range H.D).map (bytesF u.mem dig) ++
      (List.range sl).map (fun i => V (oEm + lo + db - sl + i))
    WP isa (fixedSaltBack f H) u fun u' =>
      Lay u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], u'.gpr r = u.gpr r) ∧
      (∃ V' W', Rep u'.mem F S V' W' ∧
        ∀ j < nW, j ≠ 27 → j ≠ 28 → j ≠ 29 → j ≠ 30 → W' j = W j) ∧
      u'.gpr .rax = if W 33 = 0 ∧ ∀ i < H.D,
        (lk.G.hash msg).getD i 0 = V (oEm + lo + db + i) then 1 else 0 := by
  intro msg
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hL := hH.dims.L
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c3 : oDig = 2304 := rfl
  have c5 : oRsa = 8192 := rfl
  have hml : msg.length = 8 + H.D + sl := by
    simp only [msg, List.length_append, RsaPss.zeros_length, List.length_map, List.length_range]
  have hnb1 := Nat.lt_div_mul_add (a := 8 + H.D + sl + H.P.L) (b := H.P.B) hB0
  have hnb2 := Nat.div_mul_le_self (8 + H.D + sl + H.P.L) H.P.B
  have hnb : ((8 + H.D + sl + H.P.L) / H.P.B + 1) * H.P.B ≤ 2048 := by rw [Nat.succ_mul]; omega_arith
  have hfitN : 8 + H.D + sl < ((8 + H.D + sl + H.P.L) / H.P.B + 1) * H.P.B := by rw [Nat.succ_mul]; omega_arith
  unfold fixedSaltBack fixedSaltPrefix fixedHead seqs seqs seqs seqs
  apply WP.assoc'
  apply WP.assoc'
  refine WP.seq (X86_64.WP.mono_syms (WP.keepIn (by safe_by [hashSaltLen]) (by exact Nat.zero_le 16)
    (hashSaltLen_ok hH L R (k := 36) (by decide) hsl (by omega_arith))) fun u0 ⟨⟨L0, k0, R0⟩, f0⟩ s0 => ?_)
  have hS0 := chain (u := u) rfl L.rsp (fun _ _ => rfl) f0
  apply WP.assoc'
  refine WP.seq (X86_64.WP.mono_syms (WP.keepIn (by safe_by [clearNb]) (by exact Nat.zero_le 16)
    (clearNb_ok hH L0 R0 (nbm := (8 + H.D + sl + H.P.L) / H.P.B + 1) (by simp [upd]) (Nat.succ_pos _) hnb))
    fun u1 ⟨⟨L1, k1, hcx1, R1⟩, f1⟩ s1 => ?_)
  have hS1 := chain (u := u) k0.2.2 L0.rsp hS0 f1
  refine WP.seq (X86_64.WP.mono_syms (copyDigest_ok hH L1 R1 (p := dig) (by simp [upd, hdg]) hcx1
    (fun i hi => by rw [k1.2.1, k0.2.1, k1.2.2, k0.2.2]; exact hdR i hi)
    (fun i hi j hj => Outside.ne L1 (by rw [k1.2.2, k0.2.2]; exact hdO i hi) (by omega_arith)))
    fun u2 ⟨L2, k2, R2⟩ s2 => ?_)
  have salt_src : ∀ i < sl, u2.mem (off S (oEm + lo + db - sl + i)) =
      V (oEm + lo + db - sl + i) := by
    intro i hi
    rw [R2.scr _ (by omega_arith)]
    simp only [cpV, clrV]
    rw [ifn (by omega_arith), ifn (by omega_arith)]
  apply WP.assoc'
  refine WP.seq (X86_64.WP.mono_syms (copyFixedSalt_ok hH L2 R2 (e := oEm + lo) (by simp [upd, he]) (by simp [upd, hdb])
    (by simp [upd, hsl]) hslFit (by omega_arith) (by omega_arith)
    ((k2.gpr (by decide)).trans hcx1)) fun u3 ⟨L3, k3, R3⟩ s3 => ?_)
  refine WP.seq (X86_64.WP.mono_syms (padSalt_ok L3 R3 (sl := sl) (by simp [upd, hsl]) (by omega_arith))
    fun u4 ⟨L4, k4, R4⟩ s4 => ?_)
  refine WP.seq (WP.mono (fixedHash_gen hH K L4 R4 (ℓ := 8 + H.D + sl)
    (nbm := (8 + H.D + sl + H.P.L) / H.P.B + 1) (by simp [upd]) (by simp [upd]) rfl hnb
    (by rw [s4, s3, s2, s1, s0]; exact hT.congr rfl (by simp [upd]) (by simp [upd]) (by simp [upd])) hdk)
    fun u5 ⟨L5, rd5, wr5, cs5, V5, W5, R5, hout5, hW5, hdig⟩ => ?_)
  have hdig5 := hdig msg hml (fun i hi => ?_)
  rotate_left
  · simp only [upd, cpV, clrV, msg, getD_app, List.length_append, RsaPss.zeros_length,
      List.length_map, List.length_range, getD_map_range, bytesF]
    by_cases h0 : i = 8 + H.D + sl
    · subst h0
      rw [ifp rfl, ifp rfl, ifn (by omega_arith), ifn (by omega_arith)]
      exact BitVec.zero_or.symm
    rw [ifn (by omega_arith), ifn h0]
    have oz : ∀ x : Byte, x ||| 0 = x := fun x => BitVec.or_zero
    rw [oz]
    by_cases h1 : i < 8
    · rw [ifn (show ¬(oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl) by omega_arith),
        ifn (show ¬(oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + H.D) by omega_arith),
        ifp (show oY ≤ oY + i ∧ oY + i < oY + ((8 + H.D + sl + H.P.L) / H.P.B + 1) * H.P.B by omega_arith),
        ifp (show i < 8 + H.D by omega_arith), ifp h1, RsaPss.zeros_getD]
    by_cases h2 : i < 8 + H.D
    · rw [ifn (show ¬(oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl) by omega_arith),
        ifp (show oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + H.D by omega_arith), ifp h2, ifn h1,
        ifp (show i - 8 < H.D by omega_arith), show oY + i - (oY + 8) = i - 8 by omega_arith]
      exact hS1 _ (hdO _ (by omega_arith))
    by_cases h3 : i < 8 + H.D + sl
    · rw [ifp (show oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl by omega_arith), ifn h2,
        ifp (show i - (8 + H.D) < sl by omega_arith), show oY + i - (oY + (8 + H.D)) = i - (8 + H.D) by omega_arith]
      exact salt_src _ (by omega_arith)
    · rw [ifn (show ¬(oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl) by omega_arith),
        ifn (show ¬(oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + H.D) by omega_arith),
        ifp (show oY ≤ oY + i ∧ oY + i < oY + ((8 + H.D + sl + H.P.L) / H.P.B + 1) * H.P.B by omega_arith), ifn h2,
        ifn (show ¬ i - (8 + H.D) < sl by omega_arith)]
  have h23 : W5 23 = off S (oEm + lo) := by
    rw [hW5 23 (by decide) (by decide) (by decide)]; simp [upd, he]
  have h24 : W5 24 = BitVec.ofNat 64 db := by
    rw [hW5 24 (by decide) (by decide) (by decide)]; simp [upd, hdb]
  refine WP.mono (cmpH_ok hH L5 R5 h23 h24 (by omega_arith)) fun u6 ⟨k6, hm6, hax6⟩ => ?_
  have L6 : Lay u6 F S := L5.congr (k6.gpr (by decide)) k6.2.2 (by rw [hm6])
  refine ⟨L6, k6.2.1.trans (rd5.trans (k4.2.1.trans (k3.2.1.trans (k2.2.1.trans (k1.2.1.trans k0.2.1))))),
    k6.2.2.trans (wr5.trans (k4.2.2.trans (k3.2.2.trans (k2.2.2.trans (k1.2.2.trans k0.2.2))))),
    fun r hr => ?_, ⟨V5, W5, hm6 ▸ R5, fun j hj a b c d => ?_⟩, ?_⟩
  · rw [keep_cs k6 (by decide) r hr, cs5 r hr, keep_cs k4 (by decide) r hr,
      keep_cs k3 (by decide) r hr, keep_cs k2 (by decide) r hr, keep_cs k1 (by decide) r hr,
      keep_cs k0 (by decide) r hr]
  · rw [hW5 j hj c d]; simp [upd, a, b]
  · rw [hax6]
    have h33 : W5 33 = W 33 := by
      rw [hW5 33 (by decide) (by decide) (by decide)]; simp [upd]
    have hH' : ∀ i < H.D, V5 (oDig + i) = (lk.G.hash msg).getD i 0 := fun i hi => by
      rw [map_range_getD hdig5 hi, ← lk.hash]
    have hE : ∀ i < H.D, V5 (oEm + lo + db + i) = V (oEm + lo + db + i) := fun i hi => by
      rw [hout5 _ (by omega_arith) ⟨by unfold oLen; omega_arith, by omega_arith⟩]
      simp only [upd, cpV, clrV]
      rw [ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith)]
    rw [h33]
    congr 1
    apply propext
    exact and_congr_right fun _ => forall_congr' fun i => imp_congr_right fun hi => by rw [hH' i hi, hE i hi]

end VG.Proof.RsaPss.X86_64

end

end


/-! Public dispatch between fixed and inferred salt lengths. -/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)

/-- The public fixed-length suffix agrees with the decoded suffix when
padding and length checks have succeeded. -/
theorem fixedSalt_suffix (V : Nat → Byte) (e : Nat) {db pos : Nat} (hp : pos < db) :
    (List.range (db - pos - 1)).map (fun i => V (e + db - (db - pos - 1) + i)) =
      ((List.range db).map (fun i => V (e + i))).drop (pos + 1) := by
  apply List.ext_getElem (by simp; omega_using [])
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_range, List.getElem_drop]
  congr 1
  omega_using [hp]

variable {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : Pbkdf2.Md.X86_64.HashOK H)
  (K : Pbkdf2.Md.X86_64.Callees H) {f : MdFns} (hf : MdFnsSafe f)

include hH hf in
theorem saltBack_safe : (saltBack f H).allInstrs safeI = true := by
  simp only [saltBack, fixedSaltBack, fixedSaltPrefix, fixedHead, clearNb, padSalt, genericSaltBack, seqs, clearY,
    copyDigest, copyFixedSalt, copyDb, shift, shiftPass, cmpH, Code.allInstrs, ctHash_safe hH hf, fixedHash_safe hH hf,
    rec_all, List.all_append, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include hf in
theorem saltBack_xd : (saltBack f H).x86_64Depth ≤ 8 := by
  have := ctHash_xd (H := H) hf
  have := fixedHash_xd (H := H) hf
  simp only [saltBack, fixedSaltBack, fixedSaltPrefix, fixedHead, clearNb, padSalt, genericSaltBack, seqs, clearY,
    copyDigest, copyFixedSalt, copyDb, shift, shiftPass, cmpH, byteLoop, Code.x86_64Depth, Nat.max_le]
  omega_arith

include hH K in
theorem saltBack_ok (lk : Pbkdf2.Md.X86_64.MgfLink H hH) {dn : String} (hdk : DigOK H)
    {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) (hT : HT H dn f W u.syms) {lo db pos : Nat} {dig : Addr}
    (he : W 23 = off S (oEm + lo)) (hdb : W 24 = BitVec.ofNat 64 db)
    (hpos : W 34 = BitVec.ofNat 64 pos)
    (hl : W 27 = BitVec.ofNat 64 (db - pos - 1 + (8 + H.D))) (hdg : W 37 = dig)
    (hlo : lo ≤ 1) (hdb1 : 1 ≤ db) (hpd : pos < db) (hfit : lo + db + H.D + 1 ≤ 1024)
    (hdR : ∀ i < H.D, InRegions (u.rd ++ u.wr) (dig + BitVec.ofNat 64 i) 1)
    (hdO : ∀ i < H.D, Outside u.wr F (dig + BitVec.ofNat 64 i))
    (hmatch : W 35 = 0 → W 33 = 0 → W 36 = BitVec.ofNat 64 (db - pos - 1)) :
    let msg := Spec.RsaPss.zeros 8 ++ (List.range H.D).map (bytesF u.mem dig) ++
      ((List.range db).map fun i => V (oEm + lo + i)).drop (pos + 1)
    WP isa (saltBack f H) u fun u' =>
      Lay u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], u'.gpr r = u.gpr r) ∧
      (∃ V' W', Rep u'.mem F S V' W' ∧
        ∀ j < nW, j ≠ 27 → j ≠ 28 → j ≠ 29 → j ≠ 30 →
          j ≠ 44 → j ≠ 45 → j ≠ 46 → W' j = W j) ∧
      u'.gpr .rax = if W 33 = 0 ∧ ∀ i < H.D,
        (lk.G.hash msg).getD i 0 = V (oEm + lo + db + i) then 1 else 0 := by
  intro msg
  let Q := fun u' : State =>
    Lay u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], u'.gpr r = u.gpr r) ∧
      (∃ V' W', Rep u'.mem F S V' W' ∧
        ∀ j < nW, j ≠ 27 → j ≠ 28 → j ≠ 29 → j ≠ 30 →
          j ≠ 44 → j ≠ 45 → j ≠ 46 → W' j = W j) ∧
      u'.gpr .rax = if W 33 = 0 ∧ ∀ i < H.D,
        (lk.G.hash msg).getD i 0 = V (oEm + lo + db + i) then 1 else 0
  have generic {v : State} (kv : Keep [.rax] u v) (hm : v.mem = u.mem) (hs : v.syms = u.syms) :
      WP isa (genericSaltBack f H) v Q := by
    obtain Lv := L.congr (kv.gpr (by decide)) kv.2.2 (by rw [hm])
    refine WP.mono (vback_ok hH K lk hdk Lv (hm ▸ R) (hs ▸ hT) he hdb hpos hl hdg hlo hdb1 hpd hfit
      (fun i hi => by rw [kv.2.1, kv.2.2]; exact hdR i hi)
      (fun i hi => by rw [kv.2.2]; exact hdO i hi)) fun t ⟨Lt, rd, wr, cs, ⟨Vt, Wt, Rt, hw⟩, out⟩ => ?_
    refine ⟨Lt, rd.trans kv.2.1, wr.trans kv.2.2, fun r hr => ?_,
      ⟨Vt, Wt, Rt, fun j hj _ b c d e f g => hw j hj b c d e f g⟩, ?_⟩
    · rw [cs r hr, keep_cs kv (by decide) r hr]
    · simpa only [hm] using out
  unfold saltBack
  refine WP.seq (X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun v =>
    v.mem = u.mem ∧ v.zf = some (decide (W 35 = 0))) ?_ rfl) fun v ⟨⟨hm, hz⟩, kv⟩ sv => ?_)
  · xrun [ea_sp, L.rsp, L.ld (d := sAny) (by decide), R.rd (d := sAny) 35 rfl (by decide)]
    rw [BitVec.and_self]
    rfl
  obtain Lv := L.congr (kv.gpr (by decide)) kv.2.2 (by rw [hm])
  obtain Rv : Rep v.mem F S V W := hm ▸ R
  refine WP.ite (M := isa) _ (show isa.eval .e v = _ from hz) (fun hb => ?_) (fun _ => generic kv hm sv)
  rw [decide_eq_true_eq] at hb
  refine WP.seq (X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun w =>
    w.mem = v.mem ∧ w.cf = some (decide ((W 36).toNat < db))) ?_ rfl) fun w ⟨⟨hmw, hc⟩, kw⟩ sw => ?_)
  · xrun [ea_sp, Lv.rsp, Lv.ld (d := sSlen) (by decide), Lv.ld (d := sDb) (by decide),
      Rv.rd (d := sSlen) 36 rfl (by decide), Rv.rd (d := sDb) 24 rfl (by decide), hdb]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show db < 2 ^ 64 by omega_using [hfit])]
  obtain kuw : Keep [.rax] u w := (kv.trans kw).mono (by decide)
  obtain hmu : w.mem = u.mem := hmw.trans hm
  refine WP.ite (M := isa) _ (show isa.eval .b w = _ from hc) (fun hf => ?_) (fun _ => generic kuw hmu (sw.trans sv))
  rw [decide_eq_true_eq] at hf
  obtain Lw := L.congr (kuw.gpr (by decide)) kuw.2.2 (by rw [hmu])
  refine WP.mono (fixedSaltBack_ok hH K lk Lw (hmu ▸ R) he hdb
    (show W 36 = BitVec.ofNat 64 (W 36).toNat by simp) hdg hlo hf hfit
    (fun i hi => by rw [kuw.2.1, kuw.2.2]; exact hdR i hi)
    (fun i hi => by rw [kuw.2.2]; exact hdO i hi) (by rw [sw, sv]; exact hT) hdk)
    fun t ⟨Lt, rd, wr, cs, ⟨Vt, Wt, Rt, hw⟩, out⟩ => ?_
  refine ⟨Lt, rd.trans kuw.2.1, wr.trans kuw.2.2, fun r hr => ?_,
    ⟨Vt, Wt, Rt, fun j hj a b c d _ _ _ => hw j hj a b c d⟩, ?_⟩
  · rw [cs r hr, keep_cs kuw (by decide) r hr]
  · rw [out]
    by_cases hacc : W 33 = 0
    · have hsl : (W 36).toNat = db - pos - 1 := by
        rw [hmatch hb hacc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hfit])]
      rw [hsl, fixedSalt_suffix V (oEm + lo) hpd, hmu]
    · simp only [hacc, false_and, ↓reduceIte]

end VG.Proof.RsaPss.X86_64

end

end

/-!
# RSASSA-PSS verification on x86-64: correctness

`vlogic`: what the code computes is zero exactly when the encoding is
valid, byte by byte (`VerifyCases.lean`). `verify_body`: from the entry
state, the body of the frame returns 1 exactly when `RsaPss.verify` holds,
with the callee-saved registers restored.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (pubChkContract)

theorem list_eq_iff_getD {a b : List Byte} {n : Nat} (ha : a.length = n) (hb : b.length = n) :
    a = b ↔ ∀ i < n, a.getD i 0 = b.getD i 0 := by
  constructor
  · rintro rfl _ _; rfl
  · intro h
    apply List.ext_getElem (by omega_arith)
    intro i h₁ h₂
    have := h i (by omega_arith)
    rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁,
      List.getElem?_eq_getElem h₂] at this

theorem ofNat_eq_iff {a : Nat} (ha : a < 2 ^ 64) (b : BitVec 64) : BitVec.ofNat 64 a = b ↔ a = b.toNat := by
  constructor
  · rintro rfl; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  · rintro rfl; simp

/-- What the code computes, against the checks of `verifyEncoding` (MGF1's `G`, the
digest's `H`). -/
theorem vlogic (G H : Spec.Mgf1.Hash) (hH : Proof.Mgf1.Valid H) (x mHash : List Byte) {k lo z : Nat} (fixed : Bool)
    (slen : BitVec 64) {sLen : Option Nat} (hsl : sLen = if fixed then some slen.toNat else none)
    (hx : x.length = k) (hlo : lo ≤ 1) (hfit : H.len + 2 ≤ k - lo) (hk : k ≤ 1024) :
    let em := x.drop lo
    let L := k - lo - H.len - 1
    let dbL := vDb₂ G H em L z
    let fd := decide (lz dbL < L)
    let pos := if lz dbL < L then lz dbL else 0
    let val := if lz dbL < L then dbL.getD (lz dbL) 0 else 0
    (acc1V (acc0V (x.getD (k - 1) 0) (x.getD 0 0) (x.getD lo 0) ((0xFF : Byte) >>> z) lo) fd val fixed
        (BitVec.ofNat 64 (L - pos - 1)) slen = 0 ∧
      ∀ i < H.len, (H.hash (Spec.RsaPss.zeros 8 ++ mHash ++ dbL.drop (pos + 1))).getD i 0 = (vH H em L).getD i 0) ↔
    ((lo = 1 → x.getD 0 0 = 0) ∧ EncOk₂ G H mHash em (k - lo) z sLen) := by
  dsimp only
  have hvH : (vH H (x.drop lo) (k - lo - H.len - 1)).length = H.len := by simp [vH]; omega_arith
  rw [acc1V_eq_zero, acc0V_eq_zero _ _ _ _ hlo]
  have e1 : x.getD (k - 1) 0 = (x.drop lo).getD (k - lo - 1) 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]; congr 2; omega_arith
  have e2 : x.getD lo 0 = (x.drop lo).getD 0 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero]
  rw [e1, e2]
  unfold EncOk₂
  rw [← list_eq_iff_getD (hH.2 _) hvH]
  generalize vDb₂ G H (x.drop lo) (k - lo - H.len - 1) z = dbL
  by_cases hf : lz dbL < k - lo - H.len - 1
  · rw [ifp hf, ifp hf, decide_eq_true hf, ofNat_eq_iff (by omega_arith)]
    subst hsl
    constructor
    · rintro ⟨⟨⟨hA, hP, hB⟩, hC, -, hS⟩, hH⟩
      refine ⟨hP, hA, hB, hf, hC, ?_, hH⟩
      cases fixed
      · exact .inl rfl
      · exact .inr (by rw [ifp rfl]; congr 1; have := hS rfl; omega_arith)
    · rintro ⟨hP, hA, hB, -, hC, hS, hH⟩
      refine ⟨⟨⟨hA, hP, hB⟩, hC, rfl, fun hfx => ?_⟩, hH⟩
      subst hfx
      rw [ifp rfl] at hS
      rcases hS with h | h
      · cases h
      · have := Option.some.inj h; omega_arith
  · rw [decide_eq_false hf]
    constructor
    · rintro ⟨⟨_, _, h, _⟩, _⟩; cases h
    · rintro ⟨_, _, _, h, _⟩; exact absurd h hf

/-- What `verifyK.post` asks of `rax`: verification with the hash function
`Hs` and MGF1's `Gs`. -/
def verifyOut (Hs Gs : Spec.Mgf1.Hash) (s : State) : Bool :=
  Spec.RsaPss.verify Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r8) Hs.len)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat)
    (Spec.RsaPss.expectedSaltLen (stackArg s 2) ((stackArg s 3).setWidth 32))

/-- Before the epilogue: the result in `rax`, the saved registers in their
slots. -/
structure VDone (Hs Gs : Spec.Mgf1.Hash) (s t : State) : Prop where
  L : Lay t (fb s) (stackArg s 4)
  wr : t.wr = frR s :: s.wr
  cs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r
  rbx : t.mem.readW (off (fb s) sRbx) 64 = s.gpr .rbx
  rbp : t.mem.readW (off (fb s) sRbp) 64 = s.gpr .rbp
  r12 : t.mem.readW (off (fb s) sR12) 64 = s.gpr .r12
  out : (t.gpr .rax).setWidth 32 = if verifyOut Hs Gs s then 1 else 0

variable {H : Impl.Pbkdf2.Md.X86_64.Hash}

variable {g : Impl.Mgf1.X86_64.Table.Fns} (hg : FnsSafe g)

include hg in
theorem vmid_safe : (seqs [.block acc0, mgfXor H g, .block clearTop, scanCheck H]).allInstrs safeI = true := by
  simp only [seqs, scanCheck, prefixCheck, prefixWords, prefixBytes, posScan, posCheck, Code.allInstrs,
    mgfXor_safe hg, rec_all, List.all_append, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include hg in
theorem vmid_xd : (seqs [.block acc0, mgfXor H g, .block clearTop, scanCheck H]).x86_64Depth ≤ 16 := by
  have := mgfXor_xd (H := H) hg
  simp only [seqs, scanCheck, prefixCheck, prefixWords, prefixBytes, posScan, posCheck, byteLoop, Code.x86_64Depth,
    Nat.max_le]
  omega_using [this]

theorem ite_setWidth {p : Prop} [Decidable p] {b : Bool} (h : p ↔ b = true) :
    ((if p then 1 else 0 : BitVec 64).setWidth 32) = if b then 1 else 0 := by
  by_cases hb : b = true
  · rw [ifp (h.mpr hb), ifp hb]; rfl
  · rw [ifn (fun hp => hb (h.mp hp)), ifn hb]; rfl

theorem map_range_drop {x : List Byte} {lo n : Nat} (hn : lo + n ≤ x.length) {f : Nat → Byte}
    (hf : ∀ i < n, f i = x.getD (lo + i) 0) : (List.range n).map f = (x.drop lo).take n := by
  rw [list_eq_iff_getD (n := n) (by simp) (by simp; omega_arith)]
  intro i hi
  rw [getD_map_range, ifp hi, hf i hi]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, ifp hi, List.getElem?_drop]

end VG.Proof.RsaPss.X86_64

end

end

/-!
# RSASSA-PSS verification on x86-64: the checks and the calling convention

`verify_ok`: from the entry state, `verify` returns 1 exactly when
`RsaPss.verify` holds, refusing a modulus whose first byte is zero and an
encoding too short for the digest and the salt, with the callee-saved
registers restored. `verify_correct`: it meets `verifyK`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (pubChkContract)

variable {tsH tsG : List FnTable} {Hs Gs : Spec.Mgf1.Hash}

theorem vfail_done {s t : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay t (fb s) (stackArg s 4)) (R : Rep t.mem (fb s) (stackArg s 4) V W) (hw : t.wr = frR s :: s.wr)
    (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r)
    (h41 : W 41 = s.gpr .rbx) (h42 : W 42 = s.gpr .rbp) (h43 : W 43 = s.gpr .r12) (hf : verifyOut Hs Gs s = false) :
    WP isa verifyFail t (VDone Hs Gs s) := by
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rax = 0) ?_ rfl)
    fun t' ⟨⟨hm, hax⟩, k⟩ => ?_
  · xrun [verifyFail]
  have R' : Rep t'.mem (fb s) (stackArg s 4) V W := hm ▸ R
  refine ⟨L.congr (k.gpr (by decide)) k.2.2 (by rw [hm]), k.2.2.trans hw, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [k.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide), hcs r hr]
  · rw [R'.rd (d := sRbx) 41 rfl (by decide), h41]
  · rw [R'.rd (d := sRbp) 42 rfl (by decide), h42]
  · rw [R'.rd (d := sR12) 43 rfl (by decide), h43]
  · rw [hax, hf]; rfl

/-- The modulus' first byte. -/
theorem vn0_ok {s t : State} (hp : VPre tsH tsG s) (L : Lay t (fb s) (stackArg s 4)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 4) V W) (h18 : W 18 = s.gpr .rdi) (hrd : t.rd = s.rd)
    (hf : Frame (vwrR s) s.mem t.mem) :
    WP isa (.block n0) t fun t' => Keep [.rsi, .rax] t t' ∧ t'.mem = t.mem ∧
      t'.gpr .rax = BitVec.ofNat 64 (s.mem (s.gpr .rdi)).toNat ∧
      t'.zf = some (decide ((s.mem (s.gpr .rdi)).toNat = 0)) := by
  have hk1 := hp.k1
  have hn : t.mem (s.gpr .rdi) = s.mem (s.gpr .rdi) := by
    have := hf.bytes (R := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩) (vin_apart hp.dKn hp.dns)
      (by dsimp only; have := hp.wN; omega_using []) (i := 0) (by dsimp only; omega_using [hk1])
    simpa using this
  have hin : InRegions (t.rd ++ t.wr) (s.gpr .rdi) 1 := by
    rw [hrd]
    apply hp.hrd.left
    exact ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by simp, by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [hk1]⟩
  refine WP.mono (WP.keep [.rsi, .rax] (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .rax = BitVec.ofNat 64 (s.mem (s.gpr .rdi)).toNat ∧
      t'.zf = some (decide ((s.mem (s.gpr .rdi)).toNat = 0))) ?_ rfl) fun t' ⟨h, k⟩ => ⟨k, h⟩
  xrun [n0, ea_sp, ea_at0, L.rsp, L.ld (d := sN) (by decide), R.rd (d := sN) 18 rfl (by decide), h18, hin, hn]
  rw [zext8, BitVec.and_self, ofNat_beq_zero (by have := (s.mem (s.gpr .rdi)).isLt; omega_using [])]
  exact ⟨rfl, rfl⟩

theorem expectedSaltLen_eq (slen : BitVec 64) (any : BitVec 32) :
    Spec.RsaPss.expectedSaltLen slen any = if decide (any = 0) then some slen.toNat else none := by
  unfold Spec.RsaPss.expectedSaltLen; by_cases h : any = 0 <;> simp [h]


end VG.Proof.RsaPss.X86_64
