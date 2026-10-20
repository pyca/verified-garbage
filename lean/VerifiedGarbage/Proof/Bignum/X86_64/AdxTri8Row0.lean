module
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Chain
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Sum
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8RowCore
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory

/-! # The triangular block's first row, which writes its columns

`AdxTri8.row0Core` writes each low product straight into its column and adds
the high word before it in one carry chain, the last column taking the last
high word and the carry: the columns' old values do not matter, so nothing
clears them first. The pending high word plus the carry never exceeds
`2^64 - 1`, so the last column cannot overflow. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

theorem word0_ok (s : State) {k : Nat} {hi prev col : Reg} {v : BitVec 64} {c : Bool}
    (hm : readSrc s (.mem (at_ .rbp (8*k))) = some v) (hc : s.cf = some c)
    (h1 : hi ≠ col) (h2 : prev ≠ hi) (h3 : prev ≠ col) :
    WP isa (.block (AdxTri8.word0 k hi prev col)) s fun t => ∃ c' : Bool,
      t.cf = some c' ∧
      (t.gpr col).toNat + 2^64*((t.gpr hi).toNat + c'.toNat) =
        (s.gpr .rdx).toNat*v.toNat + (s.gpr prev).toNat + c.toNat ∧
      Keeps [hi, col] s t := by
  rw [show AdxTri8.word0 k hi prev col =
    [.mulx hi col (.mem (at_ .rbp (8*k)))] ++ [.adcx col (.reg prev)] from rfl, WP.block_append_iff]
  refine WP.mono (mulx_ok s hm (fun _ h => nomatch h) h1) fun a ⟨ea, ca, _, ka⟩ => ?_
  refine WP.mono (adcx_ok a (src := .reg prev) rfl (fun _ h => nomatch h) (ca.trans hc))
    fun t ⟨ct, hct, _, et, kt⟩ => ?_
  have pa : a.gpr prev = s.gpr prev := ka.gpr (by simp [h2, h3])
  have hiT : t.gpr hi = a.gpr hi := kt.gpr (by simp [h1])
  rw [pa] at et
  refine ⟨ct, hct, ?_, (ka.trans kt).mono (by simp)⟩
  rw [hiT]
  omega

theorem last0_ok (s : State) {col prev : Reg} {c : Bool} (hc : s.cf = some c) (hne : prev ≠ col)
    (hb : (s.gpr prev).toNat + c.toNat < 2^64) :
    WP isa (.block [.mov32 col (.imm 0), .adcx col (.reg prev)]) s fun t =>
      (t.gpr col).toNat = (s.gpr prev).toNat + c.toNat ∧ Keeps [col] s t := by
  rw [show ([.mov32 col (.imm 0), .adcx col (.reg prev)] : List Instr) =
    [.mov32 col (.imm 0)] ++ [.adcx col (.reg prev)] from rfl, WP.block_append_iff]
  refine WP.mono (movZero_ok s col) fun a ⟨za, ca, _, ka⟩ => ?_
  refine WP.mono (adcx_ok a (src := .reg prev) rfl (fun _ h => nomatch h) (ca.trans hc))
    fun t ⟨_, _, _, et, kt⟩ => ?_
  have pa : a.gpr prev = s.gpr prev := ka.gpr (by simp [hne])
  rw [za, pa] at et
  simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add] at et
  exact ⟨by omega, (ka.trans kt).mono (by simp)⟩

private theorem comb {L R H C X V P Ci W T : Nat}
    (hw : L + R*(H + C) = X*V + P + Ci) (ht : T = H + C + X*W) :
    L + R*T = P + Ci + X*(V + R*W) := by grind

private theorem comb2 {L R H X V W : Nat} (hw : L + R*H = X*V) : L + R*(H + X*W) = X*(V + R*W) := by
  grind

private theorem hi_bound {L R H C X V P Ci : Nat} (hR : R = 2^64) (hX : X < R) (hV : V < R)
    (hP : P + Ci < R) (hw : L + R*(H + C) = X*V + P + Ci) : H + C < R := by
  subst hR
  have m : X*V ≤ (2^64-1)*(2^64-1) := Nat.mul_le_mul (by omega) (by omega)
  have : 2^64*(H + C) ≤ 2^64*(2^64-1) := by omega
  exact Nat.lt_of_le_of_lt (Nat.le_of_mul_le_mul_left this (by decide)) (by decide)

theorem chain0_ok (rs : List Reg) {s : State} {B : Addr} {Z e k : Nat}
    {hi other prev : Reg} {c : Bool}
    (hs : Scr s B Z) (hp : s.gpr .rbp = off B e)
    (hZ : e + 8*(k + (rs.length - 1)) ≤ Z) (hn : rs ≠ []) (hd : rs.Nodup)
    (hh : hi ≠ other) (hph : prev ≠ hi)
    (hx : hi ≠ .rdx ∧ hi ≠ .rbp ∧ other ≠ .rdx ∧ other ≠ .rbp)
    (hrs : ∀ r ∈ rs, r ≠ hi ∧ r ≠ other ∧ r ≠ prev ∧ r ≠ .rdx ∧ r ≠ .rbp)
    (hc : s.cf = some c) (hb : (s.gpr prev).toNat + c.toNat < 2^64) :
    WP isa (.block (AdxTri8.chain0 k hi other prev rs)) s fun t =>
      value t rs = (s.gpr prev).toNat + c.toNat +
        (s.gpr .rdx).toNat*wv s.mem B (e + 8*k) (rs.length - 1) ∧
      Keeps ([hi, other] ++ rs) s t := by
  induction rs generalizing s k hi other prev c with
  | nil => exact absurd rfl hn
  | cons col rest ih =>
    cases rest with
    | nil =>
      change WP isa (.block [.mov32 col (.imm 0), .adcx col (.reg prev)]) s _
      have hcol := hrs col (by simp)
      refine WP.mono (last0_ok s hc (Ne.symm hcol.2.2.1) hb) fun t ⟨et, kt⟩ => ?_
      refine ⟨?_, kt.mono (by simp)⟩
      simp only [value, et, List.length_cons, List.length_nil, Nat.sub_self, wv, Nat.mul_zero,
        Nat.add_zero]
    | cons next rest =>
      change WP isa (.block (AdxTri8.word0 k hi prev col ++
        AdxTri8.chain0 (k+1) other hi hi (next::rest))) s _
      rw [WP.block_append_iff]
      have hcol := hrs col (by simp)
      have hm := readSrc_word hs (AdxRotate8.ea_at hp (8*k))
        (show e + 8*k + 8 ≤ Z by simp only [List.length_cons] at hZ; omega)
      refine WP.mono (word0_ok s hm hc (Ne.symm hcol.1) hph (Ne.symm hcol.2.2.1))
        fun a ⟨ca, hca, ea, ka⟩ => ?_
      have hda := List.nodup_cons.mp hd
      have rdxA : a.gpr .rdx = s.gpr .rdx := ka.gpr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨Ne.symm hx.1, Ne.symm hcol.2.2.2.1⟩)
      have rbpA : a.gpr .rbp = s.gpr .rbp := ka.gpr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨Ne.symm hx.2.1, Ne.symm hcol.2.2.2.2⟩)
      have bnd : (a.gpr hi).toNat + ca.toNat < 2^64 :=
        hi_bound rfl (s.gpr .rdx).isLt (word s.mem B (e + 8*k)).isLt hb ea
      refine WP.mono (ih (s := a) (k := k+1) (hi := other) (other := hi) (prev := hi) (c := ca)
        (hs.congr ka.2.2.2) (rbpA.trans hp)
        (by simp only [List.length_cons] at hZ ⊢; omega) (by simp) hda.2 (Ne.symm hh) hh ⟨hx.2.2.1, hx.2.2.2, hx.1, hx.2.1⟩
        (fun r hr => let q := hrs r (List.mem_cons_of_mem _ hr); ⟨q.2.1, q.1, q.1, q.2.2.2.1, q.2.2.2.2⟩)
        hca bnd) fun t ⟨et, kt⟩ => ?_
      have colT : t.gpr col = a.gpr col := kt.gpr (by
        simp only [List.cons_append, List.nil_append, List.mem_cons, not_or]
        exact ⟨hcol.2.1, hcol.1, fun h => hda.1 (h ▸ by simp), fun h => hda.1 (by simp [h])⟩)
      rw [ka.2.1, rdxA] at et
      refine ⟨?_, (ka.trans kt).mono (by intro r hr; simp only [List.cons_append,
        List.nil_append, List.mem_cons] at hr ⊢; grind)⟩
      simp only [value, colT, List.length_cons, Nat.add_sub_cancel] at et ⊢
      have wsplit : wv s.mem B (e + 8*k) (rest.length + 1) =
          (word s.mem B (e + 8*k)).toNat + 2^64*wv s.mem B (e + 8*(k+1)) rest.length := by
        rw [show rest.length + 1 = 1 + rest.length by omega, wv_add]
        simp only [wv, Nat.pow_zero, Nat.mul_zero, Nat.zero_add, Nat.one_mul, Nat.add_zero, Nat.mul_one]
        rw [show e + 8*k + 8 = e + 8*(k+1) by omega]
      rw [wsplit]
      exact comb ea et

theorem row0Core_ok (rs : List Reg) {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (hp : s.gpr .rbp = off B e)
    (hZ : e + 8*rs.length ≤ Z) (hlen : 2 ≤ rs.length) (hd : rs.Nodup)
    (hrs : ∀ r ∈ rs, Safe r ∧ r ≠ .rax ∧ r ≠ .rbx ∧ r ≠ .rcx) :
    WP isa (.block (AdxTri8.row0Core rs)) s fun t =>
      value t rs = (word s.mem B (e + 8*0)).toNat*wv s.mem B (e + 8*(0+1)) (rs.length - 1) ∧
      Keeps (([.rdx,.rax,.rbx,.rsi] : List Reg)++rs) s t := by
  cases rs with
  | nil => simp at hlen
  | cons col rest =>
    simp only [List.length_cons] at hZ hlen
    have hcol := hrs col (by simp)
    change WP isa (.block (([.mov .rdx (.mem (at_ .rbp 0))] : List Instr) ++
      ((([.alu32 .xor .rax (.reg .rax)] : List Instr) ++ [.mulx .rbx col (.mem (at_ .rbp 8))]) ++
        AdxTri8.chain0 2 .rax .rbx .rbx rest))) s _
    rw [WP.block_append_iff]
    have h0 := readSrc_word hs (AdxRotate8.ea_at hp (8*0)) (show e + 8*0 + 8 ≤ Z by omega)
    refine WP.mono (movMem_ok s h0) fun a ⟨pa, _, _, ka⟩ => ?_
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (xorRax_ok a) fun b ⟨zb, cb, _, kb⟩ => ?_
    have kab := ka.trans kb
    have rbpB : b.gpr .rbp = off B e := (kab.gpr (by decide)).trans hp
    have h1 := readSrc_word (hs.congr kab.2.2.2) (AdxRotate8.ea_at rbpB 8)
      (show e + 8 + 8 ≤ Z by omega)
    rw [kab.2.1] at h1
    refine WP.mono (mulx_ok b h1 (fun _ h => nomatch h) (Ne.symm hcol.2.2.1))
      fun c' ⟨ec, cc, _, kc⟩ => ?_
    have rdxC : c'.gpr .rdx = word s.mem B (e + 8*0) := by
      rw [kc.gpr (by simp [Ne.symm hcol.1.2.2.1]), kb.gpr (by decide), pa]
    have rbpC : c'.gpr .rbp = off B e := (kc.gpr (by simp [Ne.symm hcol.1.2.1])).trans rbpB
    have hda := List.nodup_cons.mp hd
    have hrest : rest ≠ [] := by
      intro h; subst h; simp at hlen
    refine WP.mono (chain0_ok rest (k := 2) (hi := .rax) (other := .rbx) (prev := .rbx) (c := false)
      (hs.congr (kab.trans kc).2.2.2) rbpC
      (by omega) hrest hda.2 (by decide) (by decide)
      ⟨by decide, by decide, by decide, by decide⟩
      (fun r hr => let q := hrs r (List.mem_cons_of_mem _ hr); ⟨q.2.1, q.2.2.1, q.2.2.1, q.1.2.2.1, q.1.2.1⟩)
      (cc.trans cb) (by simp only [Bool.toNat_false, Nat.add_zero]; exact (c'.gpr .rbx).isLt))
      fun t ⟨et, kt⟩ => ?_
    have colT : t.gpr col = c'.gpr col := kt.gpr (by
      simp only [List.cons_append, List.nil_append, List.mem_cons, not_or]
      exact ⟨hcol.2.1, hcol.2.2.1, hda.1⟩)
    have rdxB : b.gpr .rdx = word s.mem B (e + 8*0) := by rw [kb.gpr (by decide), pa]
    rw [rdxB] at ec
    rw [(kab.trans kc).2.1, rdxC] at et
    have sub : ∀ r ∈ (([.rdx] : List Reg) ++ [.rax]) ++ ([.rbx, col] ++ ([.rax, .rbx] ++ rest)),
        r ∈ ([.rdx,.rax,.rbx,.rsi] : List Reg) ++ col :: rest := by
      intro r hr
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hr ⊢
      grind
    refine ⟨?_, ((kab.trans kc).trans kt).mono sub⟩
    have wsplit : wv s.mem B (e + 8*(0+1)) rest.length =
        (word s.mem B (e + 8)).toNat + 2^64*wv s.mem B (e + 8*2) (rest.length - 1) := by
      obtain ⟨n, hn⟩ : ∃ n, rest.length = n + 1 := ⟨rest.length - 1, by omega⟩
      rw [hn, Nat.add_sub_cancel, show n + 1 = 1 + n by omega, wv_add]
      simp only [wv, Nat.pow_zero, Nat.mul_zero, Nat.zero_add, Nat.one_mul, Nat.add_zero, Nat.mul_one]
    show (t.gpr col).toNat + 2^64*value t rest = _
    rw [colT, et, List.length_cons, Nat.add_sub_cancel, wsplit]
    simp only [Bool.toNat_false, Nat.add_zero]
    exact comb2 (by simpa only [show e + 8 = e + 8 * 1 by omega] using ec)

private theorem split_arith0 {A B R T V : Nat} (h : A+R*(B+R*T)=V) :
    (A+R*B)+(R*R)*T=V := by grind

theorem rowStep0_ok {s : State} {B : Addr} {Z w I e : Nat}
    {lo hi : Reg} {tail : List Reg}
    (hs : Scr s B Z) (hc : s.gpr .rcx=off B (slot w aAcc+16*I)) (hp : s.gpr .rbp=off B e)
    (he : e+8*(lo::hi::tail).length≤Z)
    (hout : slot w aAcc+16*I+(16+8*(2*0+2))+8≤Z)
    (hr : (lo::hi::tail).Nodup)
    (hrs : ∀ r ∈ lo::hi::tail, Safe r ∧ r≠.rax ∧ r≠.rbx ∧ r≠.rcx ∧ r≠.rdi) :
    let out := slot w aAcc+16*I+(16+8*(2*0+1))
    WP isa (AdxTri8.rowStep0 lo hi tail) s fun t =>
      wv t.mem B out 2+2^128*value t tail=
        (word s.mem B (e+8*0)).toNat*wv s.mem B (e+8*(0+1)) ((lo::hi::tail).length-1) ∧
      Outside B out 16 s.mem t.mem ∧ Keep (([.rdx,.rax,.rbx,.rsi] : List Reg)++lo::hi::tail) s t := by
  dsimp only
  unfold AdxTri8.rowStep0
  have baseSafe : ∀ r ∈ lo::hi::tail, Safe r ∧ r≠.rax ∧ r≠.rbx ∧ r≠.rcx :=
    fun r h => let q := hrs r h; ⟨q.1,q.2.1,q.2.2.1,q.2.2.2.1⟩
  refine WP.seq (WP.mono (row0Core_ok (lo::hi::tail) hs hp he (by simp) hr baseSafe)
    fun a ⟨va,ka⟩ => ?_)
  have sl := hrs lo (by simp)
  have sh := hrs hi (by simp)
  have ca : a.gpr .rcx=off B (slot w aAcc+16*I) := (ka.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,⟨sl.2.2.2.1.symm,sh.2.2.2.1.symm,
      fun h => (hrs .rcx (by simp [h])).2.2.2.1 rfl⟩⟩)).trans hc
  refine WP.mono (storeHead_ok (hs.congr ka.2.2.2) ca hout) fun t ⟨vb,ob,kb⟩ => ?_
  have tailT : value t tail=value a tail := value_congr fun r h => kb.gpr (by simp)
  rw [ka.2.1] at ob
  refine ⟨?_,ob,(ka.keep.trans kb).mono (by simp)⟩
  rw [vb,tailT]
  simp only [value] at va
  have mul : (2 : Nat)^128=2^64*2^64 := by rw [← Nat.pow_add]
  rw [mul]
  exact split_arith0 va

end VG.Proof.Bignum.X86_64.AdxTri8
