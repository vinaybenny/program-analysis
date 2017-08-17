import java.util.ArrayList;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;



import soot.Body;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.InstanceFieldRef;
import soot.jimple.AssignStmt;
import soot.jimple.GotoStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.LookupSwitchStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.TableSwitchStmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.internal.InvokeExprBox;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.BriefBlockGraph;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.DirectedGraph;

/* 
Author: Vinay Benny
Description: Implemented as part of program analysis (CS5218) Assignment 1.
Purpose: Class  for Interprocedural Taint Analysis	
Date : 25 Mar 2013
*/

public class IntraTaintAnalysis {
		
	/* Define data structure skeleton that stores statement level taint information*/
	public class TaintInform {
		String methName;
		Unit prgmStmnt;
		HashSet taintsnpshtBfore;
		HashSet taintsnpshtAftr;
		Integer taintFlag;
		
		TaintInform(String methName, Unit prgmStmnt,	HashSet taintsnpshtBfore, HashSet taintsnpshtAftr, Integer taintFlag){
			
			this.methName=methName;
			this.prgmStmnt=prgmStmnt;
			this.taintsnpshtBfore=taintsnpshtBfore;
			this.taintsnpshtAftr=taintsnpshtAftr;
			this.taintFlag=taintFlag;
		}
	}
	
	/* List of statements and their relevant taint information*/
	public static ArrayList taintInform = new ArrayList();
	

	/* Method to initialize the worklist */
	private void createWrkList(BriefUnitGraph briefUnitGraph) {
		Iterator unitgrphIter = briefUnitGraph.iterator();
		taintInform.clear();
		String methName = new String(briefUnitGraph.getBody().getMethod().getSignature());
		while (unitgrphIter.hasNext())
		{						
			Unit u = (Unit) unitgrphIter.next();
			
			taintInform.add(new TaintInform(methName, u, new HashSet(), new HashSet(), 0));
		}		
	}
	
	
	public IntraTaintAnalysis(BriefUnitGraph briefUnitGraph) {
		
		createWrkList(briefUnitGraph);
		HashSet initTaint = new HashSet();
		HashSet finalTaint = new HashSet();
		
		CDA ctrldepGrph = new CDA(briefUnitGraph);
		Integer stopIter = 1;
		Integer loopCounter = 0;
		
		/* Iterate until intra-procedural fix point reached*/
		do{
			Iterator taintInfoiter = taintInform.iterator();
			loopCounter++;
			initTaint = new HashSet();
			initTaint.addAll(finalTaint);
			while (taintInfoiter.hasNext())
			{			
				TaintInform elem = (TaintInform) taintInfoiter.next();
				Unit stmt = elem.prgmStmnt;
				Integer taintFlg = elem.taintFlag;
				Stmt statement = (Stmt) stmt;
				
				ArrayList taintList = mergeTaintInfo(briefUnitGraph, stmt);	

				
				
				if (statement instanceof IfStmt || statement instanceof TableSwitchStmt || 
						statement instanceof LookupSwitchStmt)
				{							
					Integer tainted = 0;
					elem.taintsnpshtBfore.addAll(taintList);
					elem.taintsnpshtAftr.addAll(taintList);
					for(ValueBox box : stmt.getUseBoxes())
					{
						if(taintList.contains(box.getValue().toString()))
						{
							tainted =1;
						}
					}
					if (tainted == 1)
					{
						elem.taintFlag = 1 ;
					}
				}
				
				else if (statement instanceof AssignStmt)
				{
					elem.taintsnpshtBfore.addAll(taintList);
					elem.taintsnpshtAftr.addAll(handleAssign(stmt, taintList, ctrldepGrph.CDSMap,briefUnitGraph));
				}
				
				else if (statement instanceof IdentityStmt)
				{
					elem.taintsnpshtBfore.addAll(taintList);
					elem.taintsnpshtAftr.addAll(handleIden(stmt, taintList, briefUnitGraph));
					
				}
				
				else if(statement instanceof InvokeStmt)
				{
					elem.taintsnpshtBfore.addAll(taintList);
					elem.taintsnpshtAftr.addAll(handleInvoke(stmt, taintList, briefUnitGraph));
				}
				
				 else if (statement instanceof ReturnStmt)
                 {//nothing else needed for ReturnVoid
                         elem.taintsnpshtBfore.addAll(taintList);
                         handleRet(stmt, taintList,briefUnitGraph);
                         elem.taintsnpshtAftr.addAll(taintList);
                 }

				else 
				{
					//System.out.println("Inside Nowhere stmnt "+statement);
					elem.taintsnpshtBfore.addAll(taintList);
					elem.taintsnpshtAftr.addAll(taintList);
				}
				
				finalTaint = new HashSet();
				finalTaint.addAll(taintList);				
			}
			
			/*Compare before and after taint information for checking fixpoint*/
		stopIter = compareArrays(initTaint, finalTaint);
		} while (stopIter != 0);
		printTaintInfo();
	}


	/*Handles return satements*/
	private void handleRet(Unit stmt, ArrayList taintList, BriefUnitGraph briefUnitGraph) {
       // System.out.println("inside handleRet methodname:"+stmt);
        InterTaintAnalysis.MethodInformation method = InterTaintAnalysis.findMethod(briefUnitGraph.getBody().getMethod().getSignature());
        
        for(ValueBox ret: stmt.getUseBoxes())
        {
                for(Object var: taintList)
                {
                    //System.out.println("var is "+var+"an d ret is: "+ret.getValue().toString());   
                	if(var.toString().equals(ret.getValue().toString()))
                        {
                                method.genSet.add("@return");
                               // System.out.println("@Return added: "+stmt+" & genset method is "+method.genSet);
                        }
                        else if (var.toString().contains(ret.getValue().toString()+".<"))
                        {
                                
                        	Integer fieldStart = var.toString().indexOf(".");
                        	//System.out.println("inside .< "+var);      
                            method.genSet.add("@return"+var.toString().substring(fieldStart));
                            //System.out.println("@Return.Field is added: "+"@return"+var.toString().substring(fieldStart));
                        }
                }
        }
        return;
}

	/*Handles Invoke satements*/
	private Collection handleInvoke(Unit stmt, ArrayList taintList, BriefUnitGraph briefUnitGraph) {                
        
		Stmt c = (Stmt) stmt; 
        InvokeExpr expr=c.getInvokeExpr();
        SootMethod method=expr.getMethod();
        SootClass target=method.getDeclaringClass();        
        
        //System.out.println("=====================================================================================");
        //System.out.println("getArg"+ expr.getArg(0)+"\ngetArgCount"+expr.getArgCount()+"\ngetMethodRef"+expr.getMethodRef()+"\ngetClass"+expr.getClass()
        //+"\ngetType"+expr.getType()+"\ngetUseBoxes"+        expr.getUseBoxes());
        //System.out.println("target: "+target);
        //System.out.println("=====================================================================================");
        
       
        /*Check if the method call is for java library methods*/
        if(method.isJavaLibraryMethod())
        {  
        }  
        else
        	{
        	runPreset(c,taintList);
        	InterTaintAnalysis.methodList.add(method.toString());
        	//System.out.println("LookLook! I get an User Method: "+method);
        	if (expr instanceof SpecialInvokeExpr) {
                ValueBox obj1 = (ValueBox) expr.getUseBoxes().get(0);
                String obj = obj1.getValue().toString();
                for (Object ret :InterTaintAnalysis.methodInfo.get(method.toString()).genSet)
                {
                        if(ret.toString().contains("@this"))
                        {
                        	
                                Integer fieldStart = ret.toString().indexOf(".");
                                taintList.add(obj+ret.toString().substring(fieldStart));
                                //System.out.println("Added object/Field to taintList: "+ obj+ret.toString().substring(fieldStart));
                        }
                }                
        	}
        	
        	}
        return taintList;
	}

	/*Handles Identity satements*/
	private ArrayList handleIden(Unit stmt, ArrayList taintList,
			BriefUnitGraph briefUnitGraph) {

		InterTaintAnalysis.MethodInformation method = InterTaintAnalysis.findMethod(briefUnitGraph.getBody().getMethod().getSignature());
		HashSet preset = method.preSet;

		Iterator presetiter = preset.iterator();	
		
		while(presetiter.hasNext())
		{
			String presetVal = (String) presetiter.next();
			for (ValueBox assignee : stmt.getDefBoxes())
			{
				for (ValueBox assigner : stmt.getUseBoxes())
				{
					Integer colIndex = assigner.getValue().toString().indexOf(":");
					String strLeft = assigner.getValue().toString().substring(0, colIndex);
					String strRight = assigner.getValue().toString().substring(colIndex+2); 
					String checkVar = strLeft+".<"+strRight;

					if (assigner.getValue().toString().contains(presetVal))
					{
						taintList.add(assignee.getValue().toString());
					}
					else if(presetVal.contains(checkVar))
					{
						Integer fieldStart = presetVal.indexOf(".");
						taintList.add(assignee.getValue().toString()+presetVal.substring(fieldStart));

					}
					
				}
			}
		}	

		return new ArrayList<String>(taintList);
		
	}


	private Integer compareArrays(HashSet initTaint, HashSet finalTaint) {
		// TODO Auto-generated method stub

		if(initTaint.equals(finalTaint))
		{
			return 0;
		}
		else
		{
			return 1;
		}
	}


	private ArrayList handleAssign(Unit stmt, ArrayList taintList,
			Map<Unit, HashSet<Unit>> cDSMap, BriefUnitGraph briefUnitGraph) {

		/* The below variable will be set if the assignment comes inside a tainted if statement*/
		Integer tainted = 0;
		/* The below variable will be set if at least one element on the assignment side is tainted*/
		Integer taintmarker = 0;
		Stmt statement = (Stmt) stmt;
		if (cDSMap.containsKey(stmt))
		{
			HashSet<Unit> ifList = cDSMap.get(stmt);		
			Iterator it = ifList.iterator();

			
			/* Check if the assignment statement comes inside a tainted conditional statement*/
			while (it.hasNext())
			{
				Unit ifstmt = (Unit) it.next();

				Iterator objiter = taintInform.iterator();
				while (objiter.hasNext())
				{
					TaintInform elem = (TaintInform) objiter.next();

					if (ifstmt.equals(elem.prgmStmnt) && elem.taintFlag == 1)
					{
						tainted = 1;
						taintmarker = 1;
					}
				}
			}
		}
		
		if(statement.containsInvokeExpr() && !(statement.getInvokeExpr().getMethod().isJavaLibraryMethod()))
		{
			runPreset(statement,taintList);
			String taintVar = runGenset(statement);
			
			if(taintVar != null)
			{
				taintList.add(taintVar);
			}
			
		}	
		
		
		/* Check if the assignment statement is a user input function or member of taintlist*/
		else 
		{
			for (ValueBox assignee : stmt.getDefBoxes())		
			{
				
				for (ValueBox assigner : stmt.getUseBoxes())
				{
					
					/* Ordinary Assignment handler*/
					if(assigner.getValue().toString().equals("new java.util.Scanner") ||
							assigner.getValue().toString().equals("new java.io.BufferedReader") || 
							taintList.contains(assigner.getValue().toString()) || tainted == 1 )
					{

						taintmarker = 1;
						if(assignee.getValue() instanceof soot.jimple.ArrayRef)
						{
							String varName = new String(((soot.jimple.ArrayRef) assignee.getValue()).getBase().toString());
							taintList.add(varName);
						}
						
						else
						{
							taintList.add(assignee.getValue().toString());
							if(assignee.getValue().toString().contains("this.<") && taintList.contains(assigner.getValue().toString()))
							{
								String methodName = briefUnitGraph.getBody().getMethod().getSignature();
								//System.out.println("Assignstmnt is: "+statement+" and this is added to genset"+assignee.getValue().toString());
								
								InterTaintAnalysis.methodInfo.get(methodName).genSet.add("@"+assignee.getValue().toString());
								//System.out.println("genset is: "+InterTaintAnalysis.methodInfo.get(methodName).genSet);
							}
						}					
											
						
					}				
				}
				
				/* If the tainted value in the assignee is killed, the below condition removes it from the taint list*/
				if (taintmarker == 0)
				{
					taintList.remove(assignee.getValue().toString());
				}
			}
		}

		return new ArrayList<String>(taintList);
	}



	private String runGenset(Stmt statement) {
		// TODO Auto-generated method stub
		InvokeExpr ivE = statement.getInvokeExpr();
		SootMethod meth = ivE.getMethod();
		HashSet<String> gen = InterTaintAnalysis.methodInfo.get(meth.toString()).genSet;
		String retString = null;

		
		for(Object ret1 : gen)
		{
			String ret = (String) ret1;
			
			Unit ut = (Unit)statement;		
			if(ret.equals("@return"))
			{
				for (ValueBox assignee : ut.getDefBoxes())
				{
					retString = assignee.getValue().toString();

				}				 
			}
			else if (ret.contains("@return.<"))
			{
				//System.out.println("inside @return statement");
				Integer fieldStart = ret.toString().indexOf(".");
				
				for (ValueBox assignee : ut.getDefBoxes())
				{
					retString = assignee.getValue().toString()+ret.substring(fieldStart);
				}		
				
			}
		}
		
		return retString;
	}


	private void runPreset(Stmt statement, ArrayList taintList) {
		// TODO Auto-generated method stub
		InvokeExpr ivE = statement.getInvokeExpr();
		SootMethod meth = ivE.getMethod();
		SootClass target=meth.getDeclaringClass();
		//System.out.println("MethodName is: "+meth.toString());
		InterTaintAnalysis.methodList.add(meth.toString());
		List<Value> argList= ivE.getArgs();
		//System.out.println("Args: "+ argList +"for method: "+meth.toString());
		
		Iterator iter = argList.iterator();
		Integer loopCounter = 0;
		while (iter.hasNext())
		{
			Value v = (Value) iter.next();

			if(taintList.contains(v.toString()))
			{
				InterTaintAnalysis.methodInfo.get(meth.toString()).preSet.add("@parameter"+loopCounter);
			}
			else
			{
				Iterator i = taintList.iterator();
				String chkStr = v.toString()+".<"+v.getType().toString();
				while(i.hasNext())
				{
					String taintElem = (String) i.next();		
					if (taintElem.contains(chkStr))
					{
						Integer fieldStart = taintElem.toString().indexOf(".");
						InterTaintAnalysis.methodInfo.get(meth.toString()).preSet.add("@parameter"+loopCounter+taintElem.toString().substring(fieldStart));
						
					}
					
				}
				
			}
			loopCounter++;
							
		}

		for(Object var:taintList)
		{ //for tainted Field, add them into Preset       

		                                                        
		    if(var.toString().contains(target.toString()))
		    {

		    	Integer fieldStart = var.toString().indexOf(".");
		    	InterTaintAnalysis.methodInfo.get(meth.toString()).preSet.add("@this"+var.toString().substring(fieldStart));

		    }
		}	
		
	}


	/* Method that combines and returns all the taintarrays of the predecessor units */
	private ArrayList mergeTaintInfo(BriefUnitGraph briefUnitGraph, Unit stmt) {

		List<Unit> predUnits = briefUnitGraph.getPredsOf(stmt);
		ArrayList<String> taintList = new ArrayList();
		Iterator iter = predUnits.iterator();		
		while (iter.hasNext())
		{
			Unit ut = (Unit) iter.next();
			Iterator taintInfoiter = taintInform.iterator();
			while (taintInfoiter.hasNext())
			{
				TaintInform elem = (TaintInform) taintInfoiter.next();
				if(elem.prgmStmnt.equals(ut))
				{
					//System.out.println("Original stmt: "+stmt+"Predecs Statement is: "+elem.prgmStmnt+"\n is: "+elem.taintsnpshtAftr);
					taintList.addAll(elem.taintsnpshtAftr);
				}
			}
		}

		return new ArrayList<String>(taintList);
		
	}
	
	public static void printTaintInfo() {
		Iterator taintInfoiter = taintInform.iterator();
		System.out.println("\n\n\tTaint Information\n\t-----------------\n\n");
		while (taintInfoiter.hasNext())
		{
			TaintInform taintObj = (TaintInform) taintInfoiter.next();			
			System.out.println("\n"+"Method name: "+taintObj.methName+"\nEntry: "+taintObj.taintsnpshtBfore+"\nStatement: "+taintObj.prgmStmnt+"\nExit: "+taintObj.taintsnpshtAftr+"\n");
		}
		
	}
}
	