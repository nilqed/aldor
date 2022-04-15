------------------------- sit_heugcd.as ----------------------------
#include "algebra"


HeuristicGcd(Z:IntegerCategory, P:UnivariatePolynomialAlgebra0 Z): with {
		balancedRemainder: (Z, Z) -> Z;
		heuristicGcd: (P, P) -> (Partial P, P, P);
		radixInterpolate: (Z, Z) -> P;
} == add {
	-- From Zippel, "Effective Polynomial Computation",
	-- sec. 15.1 on HeuristicGCD
	heuristicGcd(p:P, q:P):(Partial P, P, P) == {
		import from Boolean, Integer, Z, Partial P;
		zero? p => ([q], 0, 1); zero? q => ([p], 1, 0);
		TIMESTART;
		d := next min(degree p, degree q);
		(cp, p) := primitive p; (cq, q) := primitive q;
		bound := (d * 2^d)::Z * max(height p, height q);
		for i in 1..100@Integer repeat {
			e := bound + random()@Z;
			h := primitivePart radixInterpolate(e, gcd(p e, q e));
			~failed?(pquo := exactQuotient(p, h)) and
				~failed?(qquo := exactQuotient(q, h)) => {
					(g, cp, cq) := gcdquo(cp, cq);
					TIME("heuristicGcd:success at ");
					return([times!(g, h)],
						times!(cp, retract pquo),
						times!(cq, retract qquo));
			}
		}
		TIME("heuristicGcd:failure at ");
		(failed, p, q);
	}

	balancedRemainder(a:Z, b:Z):Z == {
		assert(b > 0);
		r := a rem b;
		r < b quo 2 => r;
		r - b;
	}

	-- From Zippel, "Effective Polynomial Computation",
	-- sec. 15.1 on HeuristicGCD
	radixInterpolate(point:Z, image:Z):P == {
		assert(point > 0);
		p:P := 0;
		d:Integer := 0;
		while image ~= 0 repeat {
			h := balancedRemainder(image, point);
			p := add!(p, h, d);
			image := (image - h) quo point;
			d := next d;
		}
		p;
	}
}
