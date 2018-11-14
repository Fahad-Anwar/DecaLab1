package analysis.exercise2;

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import analysis.FileState;
import analysis.FileStateFact;
import analysis.ForwardAnalysis;
import analysis.VulnerabilityReporter;
import soot.Body;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.JastAddJ.IfStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.StaticFieldRef;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JGotoStmt;
import soot.jimple.internal.JIfStmt;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JSpecialInvokeExpr;
import soot.jimple.internal.JVirtualInvokeExpr;

public class TypeStateAnalysis extends ForwardAnalysis<Set<FileStateFact>> {

	public TypeStateAnalysis(Body body, VulnerabilityReporter reporter) {
		super(body, reporter);
	}

	@Override
	protected void flowThrough(Set<FileStateFact> in, Unit unit, Set<FileStateFact> out) {
		prettyPrint(in, unit, out);
		Map<Unit, Set<FileStateFact>> unitAfter = this.getUnitToAfterFlow();
		if (unit.toString().equals("virtualinvoke $r0.<target.exercise2.File: void open()>()")
				&& method.toString().equals("<target.exercise2.FileClosed: void test2()>")) {
			System.out.println("equals");
		} else if (unit.toString().equals("virtualinvoke $r0.<target.exercise2.File: void open()>()")) {
			System.out.println("equals");
		} else if (unit.toString().equals("specialinvoke $r0.<target.exercise2.File: void <init>()>()")) { 
//				&& method.toString().equals("<target.exercise2.TestFileClosed: void test2()>")) {) {
//			assertEquals("[([$r0], Init)]", result.get(unit).toString());
			System.out.println("this");
		} else if (unit.toString().equals("virtualinvoke $r1.<target.exercise2.File: void open()>()")
				&& method.getSignature().equals("<target.exercise2.FileClosedAliasing: void test2()>")) {
			System.out.println("found");
		} else if (method.getSignature().equals("<target.exercise2.FileNotClosedAliasing: void test2()>")) {
			System.out.println("final");
		}
		if (unit instanceof JAssignStmt) {
			List<ValueBox> box2 = unit.getUseAndDefBoxes();

			ValueBox vb1 = box2.get(0);
			Value v1 = vb1.getValue();
			
			ValueBox vb2 = box2.get(1);
			Value v2 = vb2.getValue();
			v1.getType();
			if (v2 instanceof JNewExpr) {
				
				if (unitAfter.containsKey(unit)) {

					this.entryInitialFlow();
					this.getFlowAfter(unit);
					Set<FileStateFact> fState = unitAfter.get(unit);
					Set<Value> values = new HashSet<Value>();
					values.add(v1);
					FileStateFact fsf = new FileStateFact(values, FileState.Init);
					fState.add(fsf);
					unitAfter.putIfAbsent(unit, fState);
					fState.addAll(in);
					copy(fState, out);
				} 
			} else if (v2 instanceof JVirtualInvokeExpr){
				
				// check returntype of v2 -> refbox . name;
				Set<Value> values = new HashSet<Value>();
				values.add(v1);
				v2.getType();
				v2.getUseBoxes();
				SootMethod method = ((JVirtualInvokeExpr) v2).getMethod();
				method.getTags();
				method.getReturnType();
				String subSig = method.getSubSignature();
				FileStateFact fsf = null;
				Set<FileStateFact> source = unitAfter.get(unit);
				
				//may ge get unitbefore (in) statement. 
				if(subSig.equals("void close()")) {
					((JVirtualInvokeExpr) v2).getMethodRef();
					fsf = new FileStateFact(values, FileState.Close);
					source.add(fsf);
				} else if(subSig.equals("void open()")) {
					fsf = new FileStateFact(values, FileState.Open);
					source.add(fsf);
				} else {
					source.addAll(in);
				}
				
				copy(source, out);
			} else if (v1 instanceof StaticFieldRef) {
				Set<Value> values = new HashSet<Value>();
				values.add(v1);
				v2.getType();
				method.getTags();
				method.getReturnType();
				method.getSubSignature();
//				FileStateFact fsf = null;
				Set<FileStateFact> source = null;
				if(unitAfter.containsKey(unit)) {
					
					source = unitAfter.get(unit);
				}
				Iterator<FileStateFact> iterator = in.iterator();
				while(iterator.hasNext()) {
					FileStateFact next = iterator.next();
					if(next.containsAlias(v2)) {
//						fsf = new FileStateFact(values, next.getState());
						next.addAlias(v1);
					}
				}
				source.addAll(in);
				copy(source, out);
			} else if (v2 instanceof StaticFieldRef) {
				Set<Value> values = new HashSet<Value>();
				values.add(v1);
				Set<FileStateFact> source = null;
				if(unitAfter.containsKey(unit)) {
					
					source = unitAfter.get(unit);
				}
				Iterator<FileStateFact> iterator = in.iterator();
				while(iterator.hasNext()) {
					FileStateFact next = iterator.next();
					if(next.containsAlias(v2)) {
						next.addAlias(v1);
//						fsf = new FileStateFact(values, next.getState());
//						source.add(fsf);
					}
				}
				source.addAll(in);
				copy(source, out);
			} else {
				System.out.println("else1" + unit);
			}
		} else if (unit instanceof JInvokeStmt) {
			if (unitAfter.containsKey(unit)) {
				List<ValueBox> box2 = unit.getUseAndDefBoxes();

				ValueBox vb1 = box2.get(0);
				Value v1 = vb1.getValue();
				ValueBox vb2 = box2.get(1);
				Value v2 = vb2.getValue();
				if(v2 instanceof JSpecialInvokeExpr) {
					Value base = ((JSpecialInvokeExpr) v2).getBase();
					Set<Value> values = new HashSet<Value>();
					Value clonded = (Value)base.clone();
					values.add(clonded);
					
					Iterator<FileStateFact> iterator = in.iterator();
					FileStateFact factToRemove = null;
					while(iterator.hasNext()) {
						FileStateFact next = iterator.next();
						if (next.containsAlias(v1)) {
							factToRemove = next;
						}
					}
					in.remove(factToRemove);
					FileStateFact fsf = new FileStateFact(values, FileState.Init);
					in.add(fsf);
					copy(in, out);
				} else if (v2 instanceof JVirtualInvokeExpr) {
					// check returntype of v2 -> refbox . name;
					Set<Value> values = new HashSet<Value>();
					values.add(v1);					
					SootMethod method = ((JVirtualInvokeExpr) v2).getMethod();
					String subSig = method.getSubSignature();
					Value base = ((JVirtualInvokeExpr) v2).getBase();
					if(subSig.equals("void close()")) {
						FileStateFact fsf = new FileStateFact(values, FileState.Close);
						out.add(fsf);
						in.forEach(f -> {
							if(!f.containsAlias(v1)) {
								out.add(f);
								System.out.println("!contains");
							}
						});
					} else if(subSig.equals("void open()")) {
						FileStateFact copy = null;
						Iterator<FileStateFact> iterator = in.iterator();
						while(iterator.hasNext()) {
							FileStateFact next = iterator.next();
							if (next.containsAlias(base)) {
								copy = next.copy();
							} else {
								out.add(next);
							}
						}
						Set<FileStateFact> fState = unitAfter.get(unit);
						copy.updateState(FileState.Open);
						fState.add(copy);
						copy(fState, out);
					}
				}

			}
		} else if (unit instanceof ReturnVoidStmt) {
			Set<FileStateFact> flow = this.getFlowBefore(unit);
			Set<FileStateFact> source = unitAfter.get(unit);
			
			source.addAll(flow);
			copy(source, out);
		} else if(unit instanceof IfStmt){
			Set<FileStateFact> flow = this.getFlowBefore(unit);
			Set<FileStateFact> source = unitAfter.get(unit);
			new HashSet<Value>();
			flow.forEach(f -> {
				source.add(f);
				copy(source, out);
			});
		} else if(unit instanceof JIfStmt){
			Set<FileStateFact> flow = this.getFlowBefore(unit);
			Set<FileStateFact> source = unitAfter.get(unit);
			new HashSet<Value>();
			flow.forEach(f -> {
				source.add(f);
				copy(source, out);

			});
		} else if (unit instanceof JGotoStmt){
			copy(in, out);
		} else {
			System.out.println("else" + unit);
		}
		prettyPrint(in, unit, out);
	}

	@Override
	protected Set<FileStateFact> newInitialFlow() {
		return new LinkedHashSet<FileStateFact>();
	}

	@Override
	protected void copy(Set<FileStateFact> source, Set<FileStateFact> dest) {
		
		dest.addAll(source);
	}

	@Override
	protected void merge(Set<FileStateFact> in1, Set<FileStateFact> in2, Set<FileStateFact> out) {
		System.out.println("merge");
	}

}
