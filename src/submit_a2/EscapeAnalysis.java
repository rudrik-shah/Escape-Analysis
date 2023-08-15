package submit_a2;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import dont_submit.EscapeQuery;

import java.util.Map.Entry;
import java.util.Queue;

import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.PrimType;
import soot.RefLikeType;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.VoidType;
import soot.Type;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.NewExpr;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.internal.JEnterMonitorStmt;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.util.Chain;

public class EscapeAnalysis extends SceneTransformer{

	Map<Unit,DS> in;
	
	Map<SootMethod,OutSummary> outSummary;
	
	Map<SootMethod,InSummary> inSummary;
	
	UnitGraph graph;
	
	List<SootClass> teclass;
	
	List<String> textend;
	
	Map<Unit,DS> visited;
	
	int count = 0;
	
	CallGraph cg;
	
	Body b;
	
	Chain<SootClass> allClasses;
	
	List<SootMethod> allMethods;
	
	Set<SootMethod> mainWorklist;
	
	Map<String,String> ans = new HashMap<>();
	
	// Data Structure
	class DS {
		// Rho-Map => Variable -> Set of references
		Map<String,Set<String>> rho = new HashMap<>();
		
		// Sigma-Map => Class, Method, reference name -> fields -> set of references
		Map<String,Map<String,Set<String>>> sigma = new HashMap<>();
		
		// Escape-Map => List of escaped references
		Set<String> escape = new HashSet<>();
	}
	
	class InSummary{
		
		// Rho-Map => Variable -> Set of references
		Map<String,Set<String>> rho;
		
		// Sigma-Map => Class, Method, reference name -> fields -> set of references
		Map<String,Map<String,Set<String>>> sigma;
		
		// Escape-Map => List of escaped references
		Set<String> escape;
		
		InSummary(){
			
			rho = new HashMap<>();
			
			sigma = new HashMap<>();
			
			escape = new HashSet<>();
		}
	}
	
	class OutSummary {
		// Sigma-Map => Class, Method, reference name -> fields -> set of references
		Map<String,Map<String,Set<String>>> sigma = new HashMap<>();
		
		// Escape-Map => List of escaped references
		Set<String> escape = new HashSet<>();
	}
	
	public DS Union(DS d1, DS d2) {
		DS d = new DS();
		
		// Union of rho
		for(Entry<String,Set<String>> entry : d1.rho.entrySet()) {
			
			d.rho.put(entry.getKey(), new HashSet<>(entry.getValue()));
		}
		
		for(Entry<String,Set<String>> entry : d2.rho.entrySet()) {
			if(d.rho.containsKey(entry.getKey())) {
				
				Set<String> s1 = new HashSet<>();
				s1.addAll(d.rho.get(entry.getKey()));
				s1.addAll(entry.getValue());
				
				d.rho.put(entry.getKey(),s1);
				
			}
			else {
				
				d.rho.put(entry.getKey(), new HashSet<>(entry.getValue()));
			}
		}
		
		// Union of sigma
		for(Entry<String,Map<String,Set<String>>> objEntry : d1.sigma.entrySet()) {
		
			Map<String,Set<String>> m3 = new HashMap<>();
			for(Entry<String,Set<String>> fEntry : d1.sigma.get(objEntry.getKey()).entrySet()) {
				m3.put(fEntry.getKey(), new HashSet<>(fEntry.getValue()));
			}
			d.sigma.put(objEntry.getKey(), m3);
		
		}

		for(Entry<String,Map<String,Set<String>>> objEntry : d2.sigma.entrySet()) {
			
			if(d.sigma.containsKey(objEntry.getKey())) {
				
				for(Entry<String,Set<String>> fEntry : d2.sigma.get(objEntry.getKey()).entrySet()) {
					
					if(d.sigma.get(objEntry.getKey()).containsKey(fEntry.getKey())) {
						
						Set<String> s1 = new HashSet<>();
						
						s1.addAll(d.sigma.get(objEntry.getKey()).get(fEntry.getKey()));
						s1.addAll(fEntry.getValue());
						
						Map<String,Set<String>> m3 = new HashMap<>();
						m3.put(fEntry.getKey(), s1);
						
						d.sigma.put(objEntry.getKey(), m3);
					}
					
					else {
						
						Map<String,Set<String>> m3 = new HashMap<>();
						
						for(Entry<String,Set<String>> fEntry1 : d2.sigma.get(objEntry.getKey()).entrySet()) {
							m3.put(fEntry.getKey(), new HashSet<>(fEntry1.getValue()));
						}
						
						d.sigma.put(objEntry.getKey(), m3);
					}
				}
			}
			
			else {
				
				Map<String,Set<String>> m3 = new HashMap<>();
				
				for(Entry<String,Set<String>> fEntry : d2.sigma.get(objEntry.getKey()).entrySet()) {
					m3.put(fEntry.getKey(), new HashSet<>(fEntry.getValue()));
				}
				
				d.sigma.put(objEntry.getKey(), m3);
			}
		}
		
		// Union of escape list
		d.escape.addAll(d1.escape);
		d.escape.addAll(d2.escape);
		
		return d;
	}
	
	public Set<String> Reachables(String operand, DS d){
		Set<String> s = new HashSet<>();
		Queue<String> q = new LinkedList<>();
		Set<String> visited = new HashSet<>();
		
		for(String s1 : d.rho.get(operand)) {
			
			q.add(s1);
			visited.add(s1);
			s.add(s1);
		}
		
		while(!q.isEmpty()) {
			String s1 = q.poll();
			if(d.sigma.containsKey(s1)) {
				for(Entry<String,Set<String>> entry : d.sigma.get(s1).entrySet()) {
					for(String s2 : entry.getValue()) {
						if(!visited.contains(s2)) {
							q.add(s2);
							visited.add(s2);
						}
						if(!s.contains(s2)) {
							s.add(s2);
						}
					}
				}
			}
		}
		
		return s;
	}
	
	public InSummary UnionIn(InSummary d1, DS d2, String thisParam, String rightName) {
		
		// Union of rho of this pointers
		if(d1.rho.containsKey(thisParam)){
			
			if(d2.rho.containsKey(rightName)) {
				
				d1.rho.get(thisParam).addAll(d2.rho.get(rightName));
			}
		}
		else {
			
			if(d2.rho.containsKey(rightName)) {
				
				d1.rho.put(thisParam, d2.rho.get(rightName));
			}
		}
		
		// Union of sigma of this pointers
		if(d2.rho.containsKey(rightName)) {
			for(String obj : d2.rho.get(rightName)) {
				if(d1.sigma.containsKey(obj)) {
					
					for(Entry<String,Set<String>> entry : d1.sigma.get(obj).entrySet()) {
						
						if(d1.sigma.get(obj).containsKey(entry.getKey())) {
							
							d1.sigma.get(obj).get(entry.getKey()).addAll(d2.sigma.get(obj).get(entry.getKey()));
						}
						else {
							
							d1.sigma.get(obj).put(entry.getKey(), new HashSet<>(d2.sigma.get(obj).get(entry.getKey())));
						}
					}
				}
				else {
					
					if(d2.sigma.containsKey(obj)) {
					
						d1.sigma.put(obj, new HashMap<>(d2.sigma.get(obj)));
					}
				}
			}
		}
		
		// Union of escape Map
		d1.escape.addAll(d2.escape);
		
		return d1;
	}
	
	public OutSummary UnionOut(OutSummary out, DS d, String rightName) {
		
		// Union of sigma
		
		if(d.rho.containsKey(rightName)) {
			for(String obj : d.rho.get(rightName)) {	
				
				if(d.sigma.containsKey(obj)) {
					 
					for(Entry<String,Set<String>> entry : d.sigma.get(obj).entrySet()) {
						
						if(out.sigma.containsKey(obj)) {
							
							if(out.sigma.get(obj).containsKey(entry.getKey())) {
												
								out.sigma.get(obj).get(entry.getKey()).addAll(d.sigma.get(obj).get(entry.getKey()));
							}
							else {
								
								out.sigma.get(obj).put(entry.getKey(), new HashSet<>(d.sigma.get(obj).get(entry.getKey())));
							}
						}
						else {
							
							out.sigma.put(obj, new HashMap<>(d.sigma.get(obj)));
						}
					}
				}
			}
		}
		
		// Union of escape
		if(! d.escape.isEmpty()) {
			
			out.escape.addAll(d.escape);
		}
		
		return out;
	}
	
	public synchronized void ComputeIn(Unit unit, String className, String methodName) {
		
		DS d = in.get(unit);
		Stmt s = (Stmt)unit;
		
		if(s instanceof DefinitionStmt) {
			
			DefinitionStmt ds = (DefinitionStmt)s;
			
			Value leftOperand = ds.getLeftOp();
			Value rightOperand = ds.getRightOp();
			
			String leftName = className + " " + methodName + " " + leftOperand;
			String rightName = className + " " + methodName + " " + rightOperand;
			
			if(leftOperand.getType() instanceof RefLikeType) {
				if(rightOperand.getType() instanceof RefLikeType) {
					
					if(rightOperand instanceof NewExpr) {
						// x = new A();
						
						if(! visited.containsKey(unit)) {
							
							String r = "R" + count;
							count++;
							
							Set<String> ref = new HashSet<>();
							ref.add(r);
							
							d.rho.put(leftName,ref);
							
							Map<String,Set<String>> m = new HashMap<>();
							Chain<SootField> chain = ((NewExpr)rightOperand).getBaseType().getSootClass().getFields();
							for(SootField field : chain) {
								
								m.put(field.getName(), new HashSet<String>());
							}
							
							SootClass c = ((NewExpr)rightOperand).getBaseType().getSootClass();
							while(c.hasSuperclass()) {
								
								if(allClasses.contains(c.getSuperclass())) {
									
									chain = c.getSuperclass().getFields();
									for(SootField field : chain) {
										
										m.put(field.getName(), new HashSet<String>());
									}
								}
								c = c.getSuperclass();
							}
							d.sigma.put(r, m);
							
							if(textend.contains(rightOperand.getType().toString())) {
								
								d.escape.addAll(ref);
							}
						
							visited.put(unit, d);
							
						}
						
						else {
							
							Set<String> s1 = new HashSet<>();
							s1.addAll(visited.get(unit).rho.get(leftName));
							d.rho.put(leftName, s1);
							
							Map<String,Set<String>> m = new HashMap<>();
							Chain<SootField> chain = ((NewExpr)rightOperand).getBaseType().getSootClass().getFields();
							for(SootField field : chain) {
								
								m.put(field.getName(), new HashSet<String>());
							}
							d.sigma.put(visited.get(unit).rho.get(leftName).iterator().next(), m);
							
							d.escape.addAll(visited.get(unit).escape);
						}
						
						in.put(unit, d);
					}
					
					else if(rightOperand instanceof InstanceFieldRef) {
						// x = y.f;
						
						SootField field = ((InstanceFieldRef)rightOperand).getField();
						String f = field.getName();
						
						String variableName = rightOperand.toString();
						char[] c = variableName.toCharArray();
						int i = 0;
						variableName = "";
						while(c[i] != '.') {
							variableName += c[i];
							i++;
						}
						rightName = className + " " + methodName + " " + variableName;
						
						Set<String> og = new HashSet<>();
						og.add("Og");
						
						Set<String> rightRho = new HashSet<>();
						if(d.rho.containsKey(rightName))
							rightRho.addAll(d.rho.get(rightName));
						
						// If Og belongs to Rho(y), then Rho(x) = Og. No change in sigma and escape map.
						if(rightRho.contains("Og")) {
							
							d.rho.put(leftName, new HashSet<>(og));
						}
						
						else {
							
							boolean flag = true;
							
							// If one of the objects in y is escaped, then Rho(x) = Og.
							for(String temp : rightRho) {
								
								if(d.escape.contains(temp)) {
									
									d.rho.put(leftName, new HashSet<>(og));
									flag = false;
									break;
								}
							}
							
							// else perform update
							if(flag) {
								
								for(String temp: rightRho) {
									
									if(d.sigma.containsKey(temp) && d.sigma.get(temp).containsValue(f))
										rightRho.addAll(d.sigma.get(temp).get(f));
								}
								
								d.rho.put(leftName, rightRho);
							}
						}
						
						in.put(unit, d);
						
					}
					
					else if(leftOperand instanceof InstanceFieldRef) {
						// x.f = y;
						
						SootField field = ((InstanceFieldRef)leftOperand).getField();
						String f = field.getName();
						
						String variableName = leftOperand.toString();
						char[] c = variableName.toCharArray();
						int i = 0;
						variableName = "";
						while(c[i] != '.') {
							variableName += c[i];
							i++;
						}
						leftName = className + " " + methodName + " " + variableName;
						
						// If f is a static field, then y and all objects reachable from y are escaped, no change in rho, sigma.
						if(field.isStatic()) {
							
							Set<String> s1 = new HashSet<>();
							s1.addAll(d.rho.get(rightName));
							
							s1.addAll(Reachables(rightName, d));
							
							d.escape.addAll(s1);
						}
						
						else {
							
							// If one of the references of x is escaped, then y and all reachables from y are escaped.
							Set<String> s1 = new HashSet<>();
//							System.out.println(leftName);
							s1.addAll(d.rho.get(leftName)); 
							
							boolean flag = true;
							for(String temp : s1) {
								if(d.escape.contains(temp)) {
									
									Set<String> s2 = new HashSet<>();
									s2.addAll(d.rho.get(rightName));
									
									s2.addAll(Reachables(rightName, d));
									
									d.escape.addAll(s2);
									
									flag = false;
									break;
								}
							}
							
							if(flag) {
								
								if(d.rho.containsKey(leftName) && d.rho.get(leftName).contains("Og")) {
									
								}
								
								else {
								
									Set<String> s2 = new HashSet<>();
									
									for(String temp : s1) {
										
										if(d.sigma.containsKey(temp) && d.sigma.get(temp).containsKey(f)) {
										
											s2.addAll(d.sigma.get(temp).get(f));
										}
									}
									
									if(d.rho.containsKey(rightName)) {
									
										s2.addAll(d.rho.get(rightName));
									}
									
									for(String s3 : s1) {
										
										d.sigma.get(s3).put(f, s2);
									}
								}
							}
						}
					
						in.put(unit, d);
					}
					
					else if(leftOperand instanceof Local && (rightOperand instanceof Local)){
						// x = y;
						
						if(d.rho.containsKey(rightName)) {
							
							d.rho.put(leftName, new HashSet<>(d.rho.get(rightName)));
						}
						
						in.put(unit, d);
					}
					
					else if(ds.containsFieldRef()) {
						// Store in static field
						
						Set<String> s1 = new HashSet<>();
						if(d.rho.containsKey(rightName)) {
							
							s1.addAll(d.rho.get(rightName));
							
							s1.addAll(Reachables(rightName, d));
							
							d.escape.addAll(s1);
						}
						
						in.put(unit, d);
					}
					
					else {
					
						in.put(unit, d);
					}
				}
				
				else {
					
					in.put(unit, d);
				}
			}
			
			else {
				
				in.put(unit, d);
			}
		}
		
		else if(s.containsInvokeExpr() && s.getInvokeExpr().getMethod().getReturnType().equals(VoidType.v())) {
			// x.foo();
			
			List<ValueBox> vb = s.getUseBoxes();
			String rightName = "";
			String thisParamName = "";
			Value v;
			if(vb.size() > 0) {
				
				ValueBox temp = vb.get(0);
				v = temp.getValue();
				rightName = className + " " + methodName + " " + v.toString();
			}
			
			Iterator<Edge> outEdges = cg.edgesOutOf(unit);
			
			OutSummary out = new OutSummary();
			while(outEdges.hasNext()) {
				
				SootMethod target = outEdges.next().getTgt().method();
				
				if(!target.toString().contains("<init>")) {
					
					if(! target.toString().contains("java.") && ! target.toString().contains("jdk.") &&  ! target.getName().equals("start") && ! target.getName().equals("join") && ! target.getName().equals("notify") && ! target.getName().equals("notifyAll")) {
				
						OutSummary temp = outSummary.get(target);
						out = UnionOut(temp, in.get(unit), rightName);
					}
				}
			}
			
			DS temp = new DS();
			temp.rho = new HashMap<>(in.get(unit).rho);
			temp.sigma = new HashMap<>(out.sigma);
			temp.escape = new HashSet<>(out.escape);
			in.put(unit, temp);
			
			outEdges = cg.edgesOutOf(unit);
			while(outEdges.hasNext()) {
				
				SootMethod target = outEdges.next().getTgt().method();
				
				if(!target.toString().contains("<init>")) {
						
					if(! target.toString().contains("java.") && ! target.toString().contains("jdk.") &&  ! target.getName().equals("start") && ! target.getName().equals("join") && ! target.getName().equals("notify") && ! target.getName().equals("notifyAll")) {
					
						InSummary prev = inSummary.get(target);
						DS curr = in.get(unit);
						
						thisParamName = target.getDeclaringClass().toString() + " " + target.getName().toString() + " " + target.getActiveBody().getThisLocal().toString();
						
						boolean addMethod = true;
				
						// Check rho, sigma, escape maps of this pointer
						if(prev.rho.containsKey(thisParamName)){
								
							if(prev.rho.get(thisParamName).equals(curr.rho.get(rightName))) {
							
								Set<String> s1 = new HashSet<>();
								s1.addAll(curr.rho.get(rightName));
								
								boolean flag = false;
								for(String t : s1) {
									
									if(prev.sigma.containsKey(t)) {
										
										if(prev.sigma.get(t).equals(curr.sigma.get(t))) {
											
											flag = true;
										}
										else {
											
											flag = false;
											break;
										}
									}
									else {
										
										flag = false;
										break;
									}
								}
								
								if(flag) {
									
									if(prev.escape.equals(curr.escape)) {
										
										addMethod = false;
									}
								}
							}
						}
						else if(addMethod && ! curr.rho.containsKey(rightName)) {
							
							addMethod = false;
						}
						
						// If in summary is different, then add the method to main worklist and take union of all parameters
						if(addMethod) {
//							System.out.println("Rudrik");
							mainWorklist.add(target);
							
							prev = UnionIn(prev, curr, thisParamName, rightName);
							
//							System.out.println(prev.rho);
							
							inSummary.put(target, prev);
						}
						
	
					}
				}
			}
			in.put(unit, d);
		}
		
		else if(s instanceof JEnterMonitorStmt) {
			
			JEnterMonitorStmt j = (JEnterMonitorStmt)s;

			String op = j.getOp().toString();
			String leftName = className + " " + methodName + " " + op;
			
			for(String s1 : d.rho.get(leftName)) {
				
				if(d.escape.contains(s1) || s1 == "Og") {
					
					op = className + " " + methodName;
					ans.put(op, "No");
					break;
				}
				else {
					
					op = className + " " + methodName;
					ans.put(op, "Yes");
				}
			}
			
			in.put(unit, d);
		}
		
		else {
			
			in.put(unit, d);
		}
	}

	@Override
	protected synchronized void internalTransform(String phaseName, Map<String, String> options) {
		/*
		 * Implement your escape analysis here
		 */
		
		// Call Graph
		cg = Scene.v().getCallGraph();
		
		// Worklist of methods
		mainWorklist = new HashSet<>();
		// Adding main method 
		mainWorklist.add(Scene.v().getMainMethod());	
		
		// Computing all classes and  methods in the program
		allClasses = Scene.v().getApplicationClasses();
		
		allMethods = new ArrayList<>();
		for(SootClass c : allClasses) {
			
			for(SootMethod m : c.getMethods()) {
					
					allMethods.add(m);
			}
		}
//		System.out.println();
//		System.out.println("All classes "+allClasses);
//		System.out.println();
//		System.out.println("All Methods "+allMethods);
//		System.out.println();
		
		// Map to store the out summary of every function in the program
		outSummary = new HashMap<>();
		
		// Map to store the in summary of every function in the program
		inSummary = new HashMap<>();

		// Initiallizing both inSummary and OutSummary maps
		for(SootMethod m : allMethods) {
			
			outSummary.put(m, new OutSummary());
			inSummary.put(m, new InSummary());
		}
		
		// To get list of classes that extends Thread class
		SootClass tclass = Scene.v().getSootClass("java.lang.Thread");
		List<SootClass> classes = Scene.v().getActiveHierarchy().getSubclassesOf(tclass);
		
		teclass = new LinkedList<SootClass>(classes);
		teclass.removeIf(c -> c.isLibraryClass());
		
		textend = new ArrayList<>();
		for(SootClass temp : teclass) {
			textend.add(temp.toString());
		}
//		System.out.println("Thread extended classes " + textend);
		
		// In summary of a unit
		in = new HashMap<>(); 
		
		visited = new HashMap<>();
		
		while(! mainWorklist.isEmpty()) {
			
//			System.out.println();
//			System.out.println("********** New Method **********");
//			System.out.println("Method is - "+mainWorklist.iterator().next());
//			System.out.println();
			
			SootMethod currMethod = mainWorklist.iterator().next();
			mainWorklist.remove(currMethod);
			
			b = currMethod.getActiveBody();
			graph = new BriefUnitGraph(b);
			
			String className = b.getMethod().getDeclaringClass().toString();
			String methodName = b.getMethod().getName();
			
			// Worklist of units
			List <Unit> worklist = new ArrayList<>();
			
			for(Unit unit : graph) {
				worklist.add(unit);
				in.put(unit, new DS());
				// If unit is entry point, then add in summary of the function to this unit
				if(graph.getPredsOf(unit).isEmpty()) {
					
//					System.out.println("Rudrik");
					DS temp = new DS();
					temp.rho = new HashMap<>(inSummary.get(currMethod).rho);
					temp.sigma = new HashMap<>(inSummary.get(currMethod).sigma);
					temp.escape = new HashSet<>(inSummary.get(currMethod).escape);
//					System.out.println(temp.rho);
					in.put(unit, temp);
				}
			}
			
			while(! worklist.isEmpty()) {
				
//				System.out.println();
//				System.out.println("__________ Unit Start __________");
//				System.out.println("Unit is - "+worklist.get(0));
				
				Unit unit = worklist.remove(0);
				
				List<Unit> pred = new ArrayList<>();
				pred = graph.getPredsOf(unit);
				
				// DS to store for preds and current unit
				DS dsPrev = new DS();
				DS dsCurr = new DS();
				
				// Computing in for the current unit
//				System.out.println();
//				System.out.println("Predecessors");
				for(Unit u : pred) {
					
//					System.out.println(u);
					ComputeIn(u, className, methodName);
					
					dsPrev = Union(dsPrev, in.get(u));
					
//					System.out.println(u);
//					System.out.println(in.get(u).rho);
//					System.out.println(in.get(u).sigma);
//					System.out.println(in.get(u).escape);
				}
//				System.out.println();
				dsCurr = in.get(unit);
				
				boolean addSucc = true;
				if(dsPrev.rho.equals(dsCurr.rho)) {
					
					if(dsPrev.sigma.equals(dsCurr.sigma)) {
						
						if(dsPrev.escape.equals(dsCurr.escape)) {
							
							addSucc = false;
						}
					}
				}
				
				if(addSucc) {
					
					for(Unit succ : graph.getSuccsOf(unit)) {
						worklist.add(succ);
//						System.out.println("Successor Added");
					}
					
					dsPrev = Union(dsPrev, dsCurr);
					in.put(unit, dsPrev);
				}
				
				dsCurr = in.get(unit);
//				System.out.println(dsCurr.rho);
//				System.out.println(dsCurr.sigma);
//				System.out.println(dsCurr.escape);
				
//				System.out.println("__________ Unit End __________");
//				System.out.println();
			}
			
			DS ds = new DS();
			for(Unit u : graph) {
				if(graph.getSuccsOf(u).isEmpty()) {
					ds = in.get(u);
				}
			}
			
//			System.out.println();
//			System.out.println(ds.rho);
//			System.out.println(ds.sigma);
//			System.out.println(ds.escape);
//			System.out.println();
			
			OutSummary prevOut = outSummary.get(currMethod);
			
			boolean addMethod = true;
			if(ds.sigma.equals(prevOut.sigma)) {
				
				if(ds.escape.equals(prevOut.escape)) {
				
					addMethod = false;
				}
			}
			
			if(addMethod) {
				
				Iterator<Edge> inEdges = cg.edgesInto(currMethod);
				
				while(inEdges.hasNext()) {
					
					SootMethod calle = inEdges.next().getSrc().method();
					
					mainWorklist.add(calle);
				}
				
				prevOut = new OutSummary();
				prevOut.sigma = new HashMap<>(ds.sigma);
				prevOut.escape = new HashSet<>(ds.escape);
				outSummary.put(currMethod, prevOut);
			}
						
//			System.out.println("********** Method End **********");
//			System.out.println("");
		}
		
		int i = 0;
		for(EscapeQuery q : A2.queryList) {
			
			String className = q.getClassName();
			String methodName = q.getMethodName();
			
//			System.out.println(className);
//			System.out.println(methodName);
			
			for(Entry<String,String> e : ans.entrySet()) {
				
//				System.out.println(e.getKey()+" "+e.getValue());
				String key = className + " " + methodName;
				if(e.getKey().equals(key)) {
					
					A2.answers[i] = e.getValue(); 
				}
			}
			
			i++;
		}
	}
}