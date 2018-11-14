package analysis.exercise2;

import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
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
import soot.jimple.StaticFieldRef;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JReturnVoidStmt;
import soot.jimple.internal.JSpecialInvokeExpr;
import soot.jimple.internal.JVirtualInvokeExpr;

public class TypeStateAnalysis extends ForwardAnalysis<Set<FileStateFact>> {

	public TypeStateAnalysis(Body body, VulnerabilityReporter reporter) {
		super(body, reporter);
	}

	@Override
	protected void flowThrough(Set<FileStateFact> in, Unit unit, Set<FileStateFact> out) {
		if (unit instanceof JAssignStmt || unit instanceof JInvokeStmt) {
			List<ValueBox> useAndDefBoxes = unit.getUseAndDefBoxes();
			Value box1Value = useAndDefBoxes.get(0).getValue();
			Value box2Value = useAndDefBoxes.get(1).getValue();
			if (unit instanceof JAssignStmt) {
				if (box1Value instanceof StaticFieldRef || box2Value instanceof StaticFieldRef) {
					Set<Value> values = new HashSet<Value>();
					values.add(box1Value);
					Iterator<FileStateFact> iterator = in.iterator();
					while (iterator.hasNext()) {
						FileStateFact next = iterator.next();
						if (next.containsAlias(box2Value)) {
							next.addAlias(box1Value);
						}
					}
				}
				copy(in, out);
			} else if (unit instanceof JInvokeStmt) {
				if (box2Value instanceof JSpecialInvokeExpr) {
					if (((JSpecialInvokeExpr) box2Value).getMethodRef().declaringClass().isJavaLibraryClass())
						return;
					Set<Value> values = new HashSet<Value>();
					values.add(box1Value);
					FileStateFact fsf = new FileStateFact(values, FileState.Init);
					out.add(fsf);
					copy(in, out);
				} else if (box2Value instanceof JVirtualInvokeExpr) {
					SootMethod method = ((JVirtualInvokeExpr) box2Value).getMethod();
					String subSig = method.getSubSignature();
					Value base = ((JVirtualInvokeExpr) box2Value).getBase();
					FileState fileState = null;
					if (subSig.equals("void close()")) {
						fileState = FileState.Close;
					} else if (subSig.equals("void open()")) {
						fileState = FileState.Open;
					}

					Iterator<FileStateFact> iterator = in.iterator();
					while (iterator.hasNext()) {
						FileStateFact next = iterator.next();
						if (next.containsAlias(base)) {
							FileStateFact copy = next.copy();
							copy.updateState(fileState);
							out.add(copy);
						} else {
							out.add(next);
						}
					}
				}

			}
		} else if (unit instanceof JReturnVoidStmt) {
			in.forEach(fsf -> {
				if (fsf.getState().equals(FileState.Open) || fsf.getState().equals(FileState.Init)) {
					this.reporter.reportVulnerability(method.getSignature(), unit);
				}
			});
			copy(in, out);
		} else {
			copy(in, out);
		}
		prettyPrint(in, unit, out);
	}

	@Override
	protected Set<FileStateFact> newInitialFlow() {
		return new HashSet<FileStateFact>();
	}

	@Override
	protected void copy(Set<FileStateFact> source, Set<FileStateFact> dest) {
		dest.addAll(source);
	}

	@Override
	protected void merge(Set<FileStateFact> in1, Set<FileStateFact> in2, Set<FileStateFact> out) {
	}

}
