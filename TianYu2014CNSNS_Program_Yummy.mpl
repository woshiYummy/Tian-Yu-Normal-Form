
# module PolyVector()

module PolyVector()
	option object;

	local PolyVec;
	local Coefficients;
	local IsComputed;
	local Vars;

	export ModuleApply::static := proc()
		Object(PolyVector, _passed );
	end;

	export ModuleCopy::static := proc(	self::PolyVector, proto::PolyVector, inputPolyVector::Vector, inputVars::{list,Vector}, $)
		if ( _npassed < 3 ) then
			self:-PolyVec, self:-Coefficients, self:-Vars, self:-IsComputed :=
			proto:-PolyVec, proto:-Coefficients, proto:-Vars, proto:-IsComputed;
		else
			self:-PolyVec := inputPolyVector;
			self:-Vars := inputVars;
		fi;
	end;

	export ModulePrint::static := proc( self::PolyVector )
		nprintf("This is a PolyVector module.\n");
	end;

	export GetVars::static := proc(self::PolyVector)
		self:-Vars;
	end;

	export YangTransform::static := proc(n::integer, m1::integer, m2::integer, m3::integer, m4::integer)
		description "m1 is the number of eigenvalues which are zero;",
			"m2 is the pairs of eigenvalues which have zero real part;",
			"m3 is the number of eigenvalues which are negative real numbers;",
			"m4 is the pairs of eigenvalues which have negative real part.";
		local Ys,L,Transformation,i,s,s1,s2;
		if m1+2*m2+m3+2*m4<>n then
			ERROR("The number of eigenvalues is not equal to number of variables.");
		fi;
		L:=m1+m2+m3+m4;

		Transformation:=NULL;
		for i from 1 to m1 do
			Transformation:=Transformation, Ys[i];
		od;
		for i from m1+1 to m1+2*m2-1 by 2 do
			Transformation:=Transformation, (Ys[i]+Ys[i+1])/2,I*(Ys[i]-Ys[i+1])/2;
		od;
		for i from m1+2*m2+1 to m1+2*m2+m3 do
			s:=i-m1-2*m2;
			Transformation:=Transformation, Ys[i];
		od;
		for i from m1+2*m2+m3+1 to n-1 by 2 do
			Transformation:=Transformation, (Ys[i]+Ys[i+1])/2,I*(Ys[i]-Ys[i+1])/2;
		od;
		LinearAlgebra:-GenerateMatrix([Transformation],[seq(Ys[i],i=1..n)])[1];
	end proc:

	export XToY::static := proc(F::{Vector,list}, Xars::{Vector,list}, T::Matrix, Y::symbol)
		local Fs,Xs,XLs,Ys,Con;
		Fs:=convert(F,Vector);
		Xs:=convert(Xars,Vector);
		XLs:=convert(Xars,list);
		Ys:=Vector([seq(Y[i],i=1..nops(XLs))]);
		Con:=zip(`=`,XLs,convert(T.Ys,list));
		simplify(T^(-1).subs(Con,Fs));
	end proc:

	export PolyCoeff::static:=proc(self::PolyVector, {Power::integer:=1, Row::integer:=0, Degrees::list:=[]})
		option remember;
		local i;
		if nops(Degrees)=0 then
			ERROR("Please input a list of degrees.");
		fi:
		if Row=0 then
			return(Vector([seq(GenerateCoefficient(self, Power, i, Degrees),
				i=1..LinearAlgebra:-RowDimension(self:-PolyVec))]));
		else
			return(GenerateCoefficient(self, Power, Row, Degrees));
		fi;
	end;

	export GenerateCoefficient::static:=proc(self::PolyVector, Power::integer, Row::integer, Degrees::list)
		option remember;
		local i,j;
		if not type(self:-IsComputed[Power, Row, op(Degrees)], indexed) and self:-IsComputed[Power, Row, op(Degrees)] then
			return(self:-Coefficients[Power, Row, op(Degrees)]);
		fi;

		if Power=1 then
			self:-Coefficients[1, Row, op(Degrees)] := Corecoeff(self:-PolyVec[Row], self:-Vars, Degrees);
		else
			self:-Coefficients[Power, Row, op(Degrees)] := add(
				add(
					GenerateCoefficient(self, Power-1, Row, j)*
					GenerateCoefficient(self, 1, Row, Degrees-j),
					j in LessEqDegrees(i, Degrees)),
				i=(Power-1)..(convert(Degrees,`+`)-1));
		fi;
		self:-IsComputed[Power, Row, op(Degrees)]:=true;
		self:-Coefficients[Power, Row, op(Degrees)];
	end;

	export Corecoeff::static:=proc(F::polynom, Vars::{list(name),Vector(name)}, Degrees::list)
		option remember;
		local n,i,G;
		if type(Vars,list) then
			n:=nops(Vars);
		else
			n:=LinearAlgebra:-Dimension(Vars);
		fi;
		G:=F;
		for i from 1 to n do
			G:=coeff(G, Vars[i], Degrees[i]);
			if G=0 then return(0); fi;
		od;
		G;
	end;

	export LessEq::static:=proc(A::list, B::list)
		option remember;
		not hastype(A-B,'positive');
	end;

	export DegreesinTotalDegree::static:=proc(TotalDegree::integer, NumberofVars::integer)
		option remember;
		local StartInt, EndInt, i;
		StartInt:=combinat:-vectoint([TotalDegree,seq(0,i=1..NumberofVars-1)]);
		EndInt:=combinat:-vectoint([seq(0,i=1..NumberofVars-1),TotalDegree]);
		[seq(combinat:-inttovec(i,NumberofVars),i=StartInt..EndInt)];
	end;

	export LessEqDegrees::static:=proc(TotalDegree::integer, Degrees::list)
		option remember;
		local n, i;
		n:=nops(Degrees);
		[seq(`if`(LessEq(i,Degrees),i,NULL),i in DegreesinTotalDegree(TotalDegree, n))];
	end;

	export UnitDegrees::static:=proc(k::depends(integer[1..n]),n::integer)
		option remember;
		combinat:-inttovec(k,n);
	end;

	export AddDegreesEqDegrees::static:=proc(MinTotalDegree::{integer, list(integer)}, Degrees::list)
		option remember;
		local Output, i, j, k, JList, Temp;
		Output:=NULL;
		if type(MinTotalDegree, integer) then
			for i from MinTotalDegree to convert(Degrees, `+`) do
				Output:=Output, op(LessEqDegrees(i, Degrees));
			od;
			Output:=[Output];
		elif type(MinTotalDegree, list(integer)) and nops(MinTotalDegree)>1 then
			for i from 1 to nops(MinTotalDegree) do
				if i=1 then
					Output:=map(`[]`,AddDegreesEqDegrees(MinTotalDegree[i], Degrees));
				else
					Temp:=NULL;
					for j in Output do
						if convert(Degrees-convert(j,`+`),`+`)<MinTotalDegree[i] then
							next;
						fi;
						if i=nops(MinTotalDegree) then
							JList:=[Degrees-convert(j,`+`)];
						else
							JList:=AddDegreesEqDegrees(MinTotalDegree[i], Degrees-convert(j,`+`));
						fi;
						if nops(JList)=0 then
							next;
						fi;
						Temp:=Temp, seq([op(j),k],k in JList);
					od;
					Output:=[Temp];
				fi;
			od;
		else
			Output:=[[Degrees]];
		fi;
		Output;
	end;

	export DegreesFrom2ToDegrees::static := proc(Degrees::list, n::integer)
		option remember;
		local delta;
		[seq(op(DegreesinTotalDegree(delta,n)),delta=2..convert(Degrees,`+`))];
	end proc:

	export LowerBounds::static := proc(Degrees::list, r::integer, n::integer)
		option remember;
		local i;
		[seq(`if`(i<=r,Degrees[i],2*Degrees[i]),i=1..n)];
	end proc:

	export FindAndRemoveZero::static := proc(Degrees::list, n::integer)
		option remember;
		local i;
		ListTools:-Transpose([seq(`if`(Degrees[i]<>0,[i,Degrees[i]],NULL),i = 1..n)]);
	end proc:

	export RightHands1::static := proc(Gp::PolyVector, Pp::PolyVector, Row::integer, r::integer, n::integer, Degrees::list)
		option remember;
		local DeltaList, RHs1, delta, RHs1c, RHs1d, RHs1e, RHs1f, RHs1g, i, j;
		DeltaList:=DegreesFrom2ToDegrees(Degrees, n);
		RHs1:=0;
		for delta in DeltaList do
			RHs1c:=PolyCoeff(Gp,':-Row'=Row,':-Degrees'=delta);
			RHs1d:=LowerBounds(delta, r, n);
			RHs1e,RHs1f:=op(FindAndRemoveZero(RHs1d, n));
			RHs1g:=AddDegreesEqDegrees(RHs1f, Degrees);
			RHs1:=RHs1+RHs1c*add(mul(
					PolyCoeff(Pp,':-Row'=RHs1e[j],':-Power'=delta[RHs1e[j]],':-Degrees'=i[j]),
				j=1..nops(i)),i in RHs1g);
		od;
		RHs1;
	end proc:

	export TianYuFunction::static:=proc(Gp::PolyVector, Pp::PolyVector, Qp::PolyVector, Row::integer, Degrees::list)
		local r,n,i,j,k,LHs1,LHs2,LHs3,LHs4,RHs1,RHs1c,RHs1d,RHs1e,RHs1f,RHs1g,RHs2,RHs2c,RHs2d,DeltaList,delta,JM;
		r:=nops(convert(GetVars(Qp),list));
		n:=nops(convert(GetVars(Gp),list));
		LHs1:=`+`(seq(Degrees[j]*
			PolyCoeff(Pp,':-Row'=Row, ':-Degrees'=Degrees)*
			PolyCoeff(Qp,':-Row'=j,':-Degrees'=UnitDegrees(j,r)),j=1..r));
		LHs2:= - `+`(seq(
			PolyCoeff(Gp,':-Row'=Row,':-Degrees'=UnitDegrees(j,n))*
			PolyCoeff(Pp,':-Row'=j,':-Degrees'=Degrees),j=1..n));
		LHs3:=`+`(seq(
			PolyCoeff(Pp,':-Row'=Row,':-Degrees'=UnitDegrees(j,r))*
			PolyCoeff(Qp,':-Row'=j,':-Degrees'=Degrees),j=1..r));
		LHs4:=`+`(seq(seq(
				`if`(k=j,NULL,(Degrees[j]+1)*
					PolyCoeff(Pp,':-Row'=Row,
						':-Degrees'=Degrees+UnitDegrees(j,r)-UnitDegrees(k,r))*
					PolyCoeff(Qp,':-Row'=j,
						':-Degrees'=UnitDegrees(k,r))),
				k=1..r),j=1..r));
				
		RHs1:=RightHands1(Gp,Pp,Row,r,n,Degrees);
		
		RHs2:=0;
		for j from 1 to r do
			RHs2c:=AddDegreesEqDegrees([1,1],Degrees+UnitDegrees(j,r));
			RHs2d:=select((x,y)->is(convert(x[1],`+`) < convert(y,`+`) and convert(x[2],`+`) < convert(y,`+`)),RHs2c,Degrees);
			RHs2:=RHs2-
				add(k[1,j]*
					PolyCoeff(Pp,':-Row'=Row, ':-Degrees'=k[1])*
					PolyCoeff(Qp,':-Row'=j, ':-Degrees'=k[2]),
				k in RHs2d);
		od;
	
		JM:=expand(add(Degrees[j]*PolyCoeff(Qp,':-Row'=j,':-Degrees'=UnitDegrees(j,r)),j=1..r)
			-PolyCoeff(Gp,':-Row'=Row,':-Degrees'=UnitDegrees(Row,n)));
		if JM=0 then
			return(PolyCoeff(Qp,':-Row'=Row,':-Degrees'=Degrees) = RHs1+RHs2, 
				PolyCoeff(Pp,':-Row'=Row,':-Degrees'=Degrees) = 0);
		elif JM<>0 and Row <= r then
			return(PolyCoeff(Pp,':-Row'=Row,':-Degrees'=Degrees) = (RHs1+RHs2)/JM, 
				PolyCoeff(Qp,':-Row'=Row,':-Degrees'=Degrees) = 0);
		else
			return(PolyCoeff(Pp,':-Row'=Row,':-Degrees'=Degrees) = (RHs1+RHs2)/JM);
		fi;
	end proc:

	export HP::static := proc(d::integer, vars::{list,Vector}, coef, {OutputIndex::truefalse:=false})
		local n,PreList,List,l,i,Index,Out;
		if type(vars,`Vector`) then
			n:=LinearAlgebra:-Dimension(vars);
		else
			n:=nops(vars);
		fi;
		PreList:=combinat:-partition(d);
		List:=[];
		for l in PreList do
			if nops(l)=n then
				List:=[op(List),l];
			elif nops(l)>n then 
				next;
			else
				List:=[op(List),[op(l),0 $ (n-nops(l))]];
			fi;	
		od:
		Index:=map(combinat:-permute,List);
		Index:=map(op,Index);
	
		if OutputIndex then return(Index); fi;
	
		if type(coef,indexed) then
			Out:=add(op(0,coef)[op(coef),op(i)]*mul(vars[j]^i[j],j=1..nops(i)),i in Index);
		else
			Out:=add(coef[op(i)]*mul(vars[j]^i[j],j=1..nops(i)),i in Index);
		fi;
		Out;
	end proc:

	export TianYuNormalForm::static := proc(InSys::{list,Vector},InVars::{list,Vector},ZeroNum::integer, 
		PureImNum::integer, AimDegree::integer,
			{AimVarName::symbol:=u, AimRName::symbol:=r, AimTName::symbol:=thetha})
		local Funs, Vars, m, n, Origin, Jaco, J0, Uars, i, Q, H, C, q, h, c, GPV, PPV, QPV,funs,KList,j,AllFuns,
			PNormal, TNormal, TTransf, Tassume;
		Funs:=Vector(InSys);
		Vars:=Vector(InVars);
		m:=LinearAlgebra:-Dimension(Funs);
		n:=LinearAlgebra:-Dimension(Vars);
		
		Origin:=[0$n];
		Jaco:=VectorCalculus:-Jacobian(Funs,convert(Vars,list)=Origin);
		J0:=LinearAlgebra:-SubMatrix(Jaco, [1..ZeroNum], [1..ZeroNum]);
	
		Uars:=Vector([seq(AimVarName[i],i=1..ZeroNum)]);
		
		Q:=Uars+Vector(ZeroNum, i->add(HP(j, Uars, q[i]), j=2..AimDegree));
		H:=Vector(n-ZeroNum, i->add(HP(j, Uars, h[i]), j=2..AimDegree));
		C:=J0.Uars+Vector(ZeroNum, i->add(HP(j, Uars, c[i]), j=2..AimDegree));
	
		GPV:=PolyVector(Funs,Vars);
		PPV:=PolyVector(Vector([Q,H]),Uars);
		QPV:=PolyVector(C,Uars);
	
		AllFuns:=NULL;
		for j from 2 to AimDegree do
			funs[j]:=NULL;
			KList:=DegreesinTotalDegree(j, ZeroNum);
			for i from 1 to m do
				funs[j]:=funs[j],seq(TianYuFunction(GPV,PPV,QPV,i,k),k in KList);
			od;
			AllFuns:=AllFuns, op(subs([AllFuns],[funs[j]]));
		od:
		
		PNormal:=subs([AllFuns],C);

		TTransf:=[seq(AimVarName[ZeroNum-PureImNum+i]=AimRName[iquo(i+1,2)],i=1..PureImNum)];
		TNormal:=simplify(subs(TTransf, PNormal));
		Tassume:=op(zip(`::`,[seq(AimVarName[i],i=1..ZeroNum-PureImNum),seq(AimRName[i],i=1..PureImNum/2)],'real'));
		TNormal:=Vector([seq(TNormal[i], i=1..ZeroNum-PureImNum),
			seq(`if`(irem(i,2)=1, (Re(TNormal[ZeroNum-PureImNum+i]) assuming Tassume), 
			(Im(TNormal[ZeroNum-PureImNum+i-1])/(AimRName[iquo(i+1,2)]) assuming Tassume)), i=1..PureImNum)]);
		map(expand,TNormal);
	end proc:

end module:


# Example 1
(*
F:=Vector([
x[2]+x[1]^2-x[1]*x[3]+x[5]^2,
-x[1]+x[2]^2+x[1]*x[4]+x[2]^3,
-x[3]+x[1]^2,
-x[4]+x[5]+x[1]^2+x[4]*x[5],
-x[4]-x[5]+x[2]^2-2*x[4]^2
]);
T:=PolyVector:-YangTransform(5, 0, 1, 1, 1):
G:=PolyVector:-XToY(F,[seq(x[i],i=1..5)],T,y):
Test:=PolyVector:-TianYuNormalForm(G, [seq(y[i], i=1..5)],2,2,7);
*)

# Example 2
(*
F:=Vector([
-x[1]^2+2*x[1]*x[2]+3*x[1]*x[4]-x[1]*x[5]-x[2]^2+x[2]*x[4],
x[3]-x[1]^2+2*x[1]*x[3]+8*x[1]*x[4]+x[3]*x[5],
-x[2]-x[3]^2+3*x[1]*x[6]-x[3]*x[4]-6*x[4]^2-x[4]*x[6]+2*x[5]^2,
-x[4]-x[1]^2+2*x[1]*x[2]+3*x[1]*x[4]-x[1]*x[5]-x[2]^2,
-x[5]+x[6]-7*x[1]^2+2*x[1]*x[3]+3*x[1]*x[6]-x[3]*x[4]-x[4]*x[6],
-x[5]-x[6]+x[1]*x[4]-5*x[3]^2+x[3]*x[5]-4*x[4]^2+x[5]^2
]);
T:=PolyVector:-YangTransform(6, 1, 1, 1, 1):
G:=PolyVector:-XToY(F,[seq(x[i],i=1..6)],T,y):
Test:=PolyVector:-TianYuNormalForm(G, [seq(y[i], i=1..6)],3,2,5);
*)

# Example 3
(*
F:=Vector([
	x[2]+x[1]^3-x[1]^2*x[5]+x[1]^2*x[7],
	-x[1]-2*x[1]*x[3]^2,
	sqrt(2)*x[4]+x[1]^2*x[3]-4*x[5]^3,
	-sqrt(2)*x[3],
	-x[5]+(x[1]-x[5])^2,
	-x[6]+x[7]+(x[1]-x[4])^2,
	-x[6]-x[7]+(x[2]-x[6])^2
]);
T:=PolyVector:-YangTransform(7, 0, 2, 1, 1):
G:=PolyVector:-XToY(F,[seq(x[i],i=1..7)],T,y):
Test:=PolyVector:-TianYuNormalForm(G, [seq(y[i], i=1..7)],4,4,5);
*)

