import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Word
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

def value (s : State) : List Reg → Nat
  | [] => 0
  | r::rs => (s.gpr r).toNat+2^64*value s rs

def Safe (r : Reg) : Prop := r≠.rsi ∧ r≠.rbp ∧ r≠.rdx ∧ r≠.rcx

theorem value_congr {s t : State} {rs : List Reg} (h : ∀ r ∈ rs, t.gpr r=s.gpr r) : value t rs=value s rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => rw [value,value,h r (by simp),ih (fun r hr => h r (by simp [hr]))]

private theorem append_arith {L L' R H C O X P D U U' Q F A Ci Oi : Nat}
    (word : L'+R*(H+C+O)=L+X*D+P+Ci+Oi)
    (tail : U'+Q*F=U+X*A+H+C+O) :
    L'+R*U'+(R*Q)*F=(L+R*U)+X*(D+R*A)+P+Ci+Oi := by grind

theorem chain_ok (rs : List Reg) {s : State} {B : Addr} {Z e k : Nat}
    {hi other prev : Reg} {c o : Bool}
    (hs : Scr s B Z) (hp : s.gpr .rbp=off B e) (hz : s.gpr .rcx=0)
    (hZ : e+8*(k+(rs.length-1)) ≤ Z) (hn : rs≠[]) (hd : rs.Nodup)
    (hh : Safe hi) (ho' : Safe other) (hne : hi≠other) (hp1 : prev≠hi) (hp2 : prev≠.rsi)
    (hrs : ∀ r ∈ rs, Safe r ∧ r≠hi ∧ r≠other ∧ r≠prev)
    (hc : s.cf=some c) (ho : s.of=some o) :
    WP isa (.block (AdxTri8.chain k hi other prev rs)) s fun t => ∃ c' o' : Bool,
      t.cf=some c' ∧ t.of=some o' ∧
      value t rs+2^(64*rs.length)*(c'.toNat+o'.toNat)=
        value s rs+(s.gpr .rdx).toNat*wv s.mem B (e+8*k) (rs.length-1)+
          (s.gpr prev).toNat+c.toNat+o.toNat ∧ Keeps ([hi,other,.rsi]++rs) s t := by
  induction rs generalizing s k hi other prev c o with
  | nil => exact False.elim (hn rfl)
  | cons col rs ih =>
    cases rs with
    | nil =>
      have cp := (hrs col (by simp)).2.2.2
      refine WP.mono (close_ok s hc ho hz (Ne.symm cp)) fun t ⟨ct,ot,hct,hot,eq,kt⟩ => ?_
      refine ⟨ct,ot,hct,hot,?_,kt.mono (by simp)⟩
      simpa only [value,List.length_cons,List.length_nil,Nat.mul_one,Nat.sub_self,wv,
        Nat.mul_zero,Nat.add_zero] using eq
    | cons next rest =>
      have cs := hrs col (by simp)
      have nd : col∉next::rest ∧ (next::rest).Nodup := List.nodup_cons.mp hd
      have hkZ : e+8*k+8 ≤ Z := by simp only [List.length_cons] at hZ; omega
      have hm : readSrc s (.mem (at_ .rbp (8*k)))=some (word s.mem B (e+8*k)) :=
        readSrc_word hs (AdxRotate8.ea_at hp (8*k)) hkZ
      simp only [AdxTri8.chain]
      rw [WP.block_append_iff]
      refine WP.mono (word_ok s hm hc ho hh.1 cs.2.1 cs.1.1 hp1 hp2 cs.2.2.2.symm)
        fun a ⟨ca,oa,hca,hoa,eq,ka⟩ => ?_
      have pa : a.gpr .rbp=off B e := (ka.gpr (by simp [Ne.symm hh.2.1,Ne.symm cs.1.2.1])).trans hp
      have za : a.gpr .rcx=0 := (ka.gpr (by simp [Ne.symm hh.2.2.2,Ne.symm cs.1.2.2.2])).trans hz
      refine WP.mono (ih (hs.congr ka.2.2.2) pa za (by simp only [List.length_cons] at *; omega)
        (by simp) nd.2 ho' hh hne.symm hne hh.1 ?_ hca hoa) fun t ⟨ct,ot,hct,hot,et,kt⟩ => ?_
      · intro r hr
        have h := hrs r (by simp [hr])
        exact ⟨h.1,h.2.2.1,h.2.1,h.2.1⟩
      have caPres : a.gpr .rdx=s.gpr .rdx := ka.gpr (by simp [Ne.symm hh.2.2.1,Ne.symm cs.1.2.2.1])
      have tailPres : value a (next::rest)=value s (next::rest) := value_congr (by
        intro r hr
        have h := hrs r (by simp [hr])
        exact ka.gpr (by simp [h.2.1,h.1.1,show r≠col by intro e; subst r; exact nd.1 hr]))
      have colPres : t.gpr col=a.gpr col := kt.gpr (by simp [cs.2.1,cs.2.2.1,cs.1.1,nd.1])
      rw [caPres,ka.2.1,tailPres] at et
      refine ⟨ct,ot,hct,hot,?_,(ka.trans kt).mono (by
        intro r hr
        simp only [List.mem_append] at hr ⊢
        rcases hr with h | h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl | rfl <;> simp
        · rcases h with h | h
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl | rfl <;> simp
          · exact Or.inr (List.mem_cons_of_mem _ h))⟩
      rw [show value t (col::next::rest)=(t.gpr col).toNat+2^64*value t (next::rest) from rfl,
        show value s (col::next::rest)=(s.gpr col).toNat+2^64*value s (next::rest) from rfl,colPres,show 64*(col::next::rest).length=64+64*(next::rest).length by simp; omega,Nat.pow_add]
      have split : wv s.mem B (e+8*k) ((col::next::rest).length-1)=
          (word s.mem B (e+8*k)).toNat+2^64*wv s.mem B (e+8*(k+1)) ((next::rest).length-1) := by
        rw [show (col::next::rest).length-1=1+((next::rest).length-1) by simp; omega,wv_add]
        simp only [wv,Nat.mul_zero,Nat.add_zero,Nat.zero_add,Nat.pow_zero,Nat.one_mul,Nat.mul_one]
        rw [show e+8*k+8=e+8*(k+1) by omega]
      rw [split]
      exact append_arith eq et

end VG.Proof.Bignum.X86_64.AdxTri8
