package analysis.exercise2;

import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.Collections;
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
import soot.SootMethodRef;
import soot.Type;
import soot.Unit;
import soot.UnitBox;
import soot.UnitPrinter;
import soot.Value;
import soot.ValueBox;
import soot.JastAddJ.IfStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JGotoStmt;
import soot.jimple.internal.JIfStmt;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JNeExpr;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JSpecialInvokeExpr;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.tagkit.Tag;
import soot.util.Switch;

public class TypeStateAnalysis extends ForwardAnalysis<Set<FileStateFact>> {

	public TypeStateAnalysis(Body body, VulnerabilityReporter reporter) {
		super(body, reporter);
	}

	@Override
	protected void flowThrough(Set<FileStateFact> in, Unit unit, Set<FileStateFact> out) {
		prettyPrint(in, unit, out);
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
		}
		if (unit instanceof JAssignStmt) {
			SootMethod flow = this.method;
			List<ValueBox> box2 = unit.getUseAndDefBoxes();

			ValueBox vb1 = box2.get(0);
			Value v1 = vb1.getValue();
			
			ValueBox vb2 = box2.get(1);
			Value v2 = vb2.getValue();
			Type v1Type = v1.getType();
			if (v2 instanceof JNewExpr) {
				
				Map<Unit, Set<FileStateFact>> unitAfter = this.getUnitToAfterFlow();
				if (unitAfter.containsKey(unit)) {

					Set<FileStateFact> initial = this.entryInitialFlow();
					Set<FileStateFact> filter = this.getFlowAfter(unit);
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
				Map<Unit, Set<FileStateFact>> unitAfter = this.getUnitToAfterFlow();
				// check returntype of v2 -> refbox . name;
				Set<Value> values = new HashSet<Value>();
				values.add(v1);
				Type type = v2.getType();
				List<Value> args = ((JVirtualInvokeExpr) v2).getArgs();
				Value base = ((JVirtualInvokeExpr) v2).getBase();
				List<ValueBox> useBoxes = v2.getUseBoxes();
				ValueBox baseBox = ((JVirtualInvokeExpr) v2).getBaseBox();
				SootMethod method = ((JVirtualInvokeExpr) v2).getMethod();
				List<Tag> tags = method.getTags();
				Type returnType = method.getReturnType();
				String subSig = method.getSubSignature();
				FileStateFact fsf = null;
				Set<FileStateFact> source = unitAfter.get(unit);
				
				//may ge get unitbefore (in) statement. 
				if(subSig.equals("void close()")) {
					SootMethodRef methodRef = ((JVirtualInvokeExpr) v2).getMethodRef();
					fsf = new FileStateFact(values, FileState.Close);
					source.add(fsf);
				} else if(subSig.equals("void open()")) {
					fsf = new FileStateFact(values, FileState.Open);
					source.add(fsf);
				} else {
//					values.remove(v1);
//					values.add(base);
//					in.forEach(f -> {
//						
//					});
					source.addAll(in);
				}
				
				copy(source, out);
			} else {
				System.out.println("else1");
			}
		} else if (unit instanceof JInvokeStmt) {
			SootMethod mehtod = this.method;
			Map<Unit, Set<FileStateFact>> unitAfter = this.getUnitToAfterFlow();
			if (unitAfter.containsKey(unit)) {
//				Set<FileStateFact> initial2 = this.entryInitialFlow();
//				Set<FileStateFact> fState = unitAfter.get(unit);
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
					Type type = v2.getType();
					List<Value> args = ((JVirtualInvokeExpr) v2).getArgs();
					List<ValueBox> useBoxes = v2.getUseBoxes();
					ValueBox baseBox = ((JVirtualInvokeExpr) v2).getBaseBox();
					SootMethod method = ((JVirtualInvokeExpr) v2).getMethod();
					List<Tag> tags = method.getTags();
					Type returnType = method.getReturnType();
					String subSig = method.getSubSignature();
					Value base = ((JVirtualInvokeExpr) v2).getBase();
					Set<FileStateFact> before = this.getFlowBefore(unit);
					Set<FileStateFact> whatsIn = in;
					if(subSig.equals("void close()")) {
//						SootMethodRef methodRef = ((JVirtualInvokeExpr) v2).getMethodRef();
//						fsf = new FileStateFact(values, FileState.Close);
						Iterator<FileStateFact> iterator = in.iterator();
						FileStateFact factToRemove = null;
						while(iterator.hasNext()) {
							FileStateFact next = iterator.next();
							if (next.containsAlias(base)) {
								factToRemove = next;
							}
						}
//						in.remove(factToRemove);
//						in.add(new FileStateFact(values, FileState.Close));
						FileStateFact fsf = new FileStateFact(values, FileState.Close);
						out.add(fsf);
//						in.forEach(f -> {
//							if(f.containsAlias(base)) {
//								in.remove(f);								
//								FileStateFact fsf = ;
//								in.add(fsf);
//							}
//						});
						in.forEach(f -> {
							if(!f.containsAlias(v1)) {
								out.add(f);
								System.out.println("!contains");
							}
						});
//						copy(in, out);
					} else if(subSig.equals("void open()")) {
//						in.forEach(f -> {
//							if(f.containsAlias(base)) {
//								f.updateState(FileState.Open);
//							}
//						});
						Iterator<FileStateFact> iterator = in.iterator();
						FileStateFact factToRemove = null;
						while(iterator.hasNext()) {
							FileStateFact next = iterator.next();
							if (next.containsAlias(base)) {
								factToRemove = next;
							}
						}
//						Value cloned = (Value)v1.clone();
						values = new HashSet<Value>();
						values.add(v1);
						
						Set<FileStateFact> fState = unitAfter.get(unit);
						FileStateFact fsf = new FileStateFact(values, FileState.Open);
						fState.add(fsf);
//						unitAfter.putIfAbsent(unit, fState);
//						fState.addAll(in);
						copy(fState, out);
						
//						in.remove(factToRemove);
//						in.add(fsf);
//						fsf = new FileStateFact(values, FileState.Open);
					}
//					Set<FileStateFact> source = unitAfter.get(unit);
//					source.addAll(in);
//					source.add(fsf);
					
				}

			}
			// Set<FileStateFact> filter = this.getFlowAfter(unit);
			// filter.add(new FileStateFact(aliases, state))
		} else if (unit instanceof ReturnVoidStmt) {
			SootMethod m  = this.method;
			Map<Unit, Set<FileStateFact>> unitAfter = this.getUnitToAfterFlow();
			Set<FileStateFact> flow = this.getFlowBefore(unit);
			Set<FileStateFact> source = unitAfter.get(unit);
			
			source.addAll(flow);
//			FileStateFact fsf = new FileStateFact(values, FileState.Open);
//			flow.forEach(f -> {
////				if(f.getState().equals(FileState.Open)) {
//					source.add(f);
//					copy(source, out);
////				}
//				
//			});
//			FileStateFact next = flow.iterator().next();
//			source.add(next);
			copy(source, out);
			
			
			
		} else if(unit instanceof IfStmt){
			SootMethod m  = this.method;
			Map<Unit, Set<FileStateFact>> unitAfter = this.getUnitToAfterFlow();
			Set<FileStateFact> flow = this.getFlowBefore(unit);
			Set<FileStateFact> source = unitAfter.get(unit);
			Set<Value> values = new HashSet<Value>();
//			FileStateFact fsf = new FileStateFact(values, FileState.Open);
			flow.forEach(f -> {
//				if(f.getState().equals(FileState.Open)) {
					source.add(f);
					copy(source, out);
//				}
				
			});
		} else if(unit instanceof JIfStmt){
			SootMethod m  = this.method;
			Map<Unit, Set<FileStateFact>> unitAfter = this.getUnitToAfterFlow();
			Set<FileStateFact> flow = this.getFlowBefore(unit);
			Set<FileStateFact> source = unitAfter.get(unit);
			Set<Value> values = new HashSet<Value>();
//			FileStateFact fsf = new FileStateFact(values, FileState.Open);
			flow.forEach(f -> {
//				if(f.getState().equals(FileState.Open)) {
					source.add(f);
					copy(source, out);
//				}
				
			});
		} else if (unit instanceof JGotoStmt){
			copy(in, out);
			System.out.println("goto");
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
