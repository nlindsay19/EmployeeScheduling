package solver.cp;

import ilog.cp.*;

import ilog.concert.*;

import java.io.File;
import java.io.FileNotFoundException;

import java.util.Scanner;

public class CPInstance
{
  // BUSINESS parameters
  int numWeeks;
  int numDays;
  int numEmployees;
  int numShifts;
  int numIntervalsInDay;
  int[][] minDemandDayShift;
  int minDailyOperation;

  // EMPLOYEE parameters
  int minConsecutiveWork;
  int maxDailyWork;
  int minWeeklyWork;
  int maxWeeklyWork;
  int maxConsecutiveNightShift;
  int maxTotalNightShift;

  // ILOG CP Solver
  IloCP cp;

  public OldCPInstance(String fileName)
  {
    try
    {
      Scanner read = new Scanner(new File(fileName));

      while (read.hasNextLine())
      {
        String line = read.nextLine();
        String[] values = line.split(" ");
        if(values[0].equals("Business_numWeeks:"))
        {
          numWeeks = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Business_numDays:"))
        {
          numDays = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Business_numEmployees:"))
        {
          numEmployees = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Business_numShifts:"))
        {
          numShifts = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Business_numIntervalsInDay:"))
        {
          numIntervalsInDay = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Business_minDemandDayShift:"))
        {
          int index = 1;
          minDemandDayShift = new int[numDays][numShifts];
          for(int d=0; d<numDays; d++)
            for(int s=0; s<numShifts; s++)
              minDemandDayShift[d][s] = Integer.parseInt(values[index++]);
        }
        else if(values[0].equals("Business_minDailyOperation:"))
        {
          minDailyOperation = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Employee_minConsecutiveWork:"))
        {
          minConsecutiveWork = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Employee_maxDailyWork:"))
        {
          maxDailyWork = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Employee_minWeeklyWork:"))
        {
          minWeeklyWork = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Employee_maxWeeklyWork:"))
        {
          maxWeeklyWork = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Employee_maxConsecutiveNigthShift:"))
        {
          maxConsecutiveNightShift = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Employee_maxTotalNigthShift:"))
        {
          maxTotalNightShift = Integer.parseInt(values[1]);
        }
      }
    }
    catch (FileNotFoundException e)
    {
      System.out.println("Error: file not found " + fileName);
    }
  }

  public void solve()
  {
    try
    {
      cp = new IloCP();

      // TODO: Employee Scheduling Model Goes Here

      // Important: Do not change! Keep these parameters as is
      cp.setParameter(IloCP.IntParam.Workers, 1);
      cp.setParameter(IloCP.DoubleParam.TimeLimit, 300);
      // cp.setParameter(IloCP.IntParam.SearchType, IloCP.ParameterValues.DepthFirst);
      // IloIntVar S = cp.intVar(1, 9);
      // IloIntVar E = cp.intVar(0, 9);
      // IloIntExpr SEND = cp.sum(cp.prod(1000, S), cp.sum(cp.prod(100, E), cp.sum(cp.prod(10, N), D)));
      // IloIntExpr MORE   = cp.sum(cp.prod(1000, M), cp.sum(cp.prod(100, O), cp.sum(cp.prod(10,R), E)));
      // IloIntExpr[] clique1 = new IloIntExpr[3];

      IloIntVar[][] shifts_array = new IloIntVar[numEmployees][numDays];
      for (int i = 0; i < numEmployees; i++) {
        for (int j = 0; j < numDays; j++) {
          shifts_array[i][j] = cp.intVar(0,3);
        }
      }

      IloIntVar[][] night_shifts_array = new IloIntVar[numEmployees][numDays];
      for (int i = 0; i < numEmployees; i++) {
        for (int j = 0; j < numDays; j++) {
          night_shifts_array[i][j] = cp.intVar(0,1);
        }
      }
      for (int i = 0; i < numEmployees; i++) {
        IloLinearNumExpr totalNightShifts = cp.linearNumExpr();
        for (int j = 0; j < numDays; j++) {
          totalNightShifts.addTerm(1,night_shifts_array[i][j]);
          cp.add(cp.imply(cp.eq(shifts_array[i][j], 1), cp.eq(night_shifts_array[i][j], 1)));
        }
        cp.add(cp.le(totalNightShifts, maxTotalNightShift));
      }

      for (int j = 0; j < numDays; j++) {
        IloLinearNumExpr totalNightsToday = cp.linearNumExpr();
        for (int i = 0; i < numEmployees; i++) {

          totalNightsToday.addTerm(1, night_shifts_array[i][j]);
        }
        cp.add(cp.ge(totalNightsToday, minDemandDayShift[j][1]));
      }



      IloIntVar[][] day_shifts_array = new IloIntVar[numEmployees][numDays];
      for (int i = 0; i < numEmployees; i++) {
        for (int j = 0; j < numDays; j++) {
          day_shifts_array[i][j] = cp.intVar(0,1);
        }
      }
      for (int i = 0; i < numEmployees; i++) {
        for (int j = 0; j < numDays; j++) {
          cp.add(cp.imply(cp.eq(shifts_array[i][j], 2), cp.eq(day_shifts_array[i][j], 1)));
        }
      }
      for (int j = 0; j < numDays; j++) {
        IloLinearNumExpr totalDaysToday = cp.linearNumExpr();
        for (int i = 0; i < numEmployees; i++) {
          totalDaysToday.addTerm(1, day_shifts_array[i][j]);
        }
        cp.add(cp.ge(totalDaysToday, minDemandDayShift[j][2]));
      }

      IloIntVar[][] evening_shifts_array = new IloIntVar[numEmployees][numDays];
      for (int i = 0; i < numEmployees; i++) {
        for (int j = 0; j < numDays; j++) {
          evening_shifts_array[i][j] = cp.intVar(0,1);
        }
      }
      for (int i = 0; i < numEmployees; i++) {
        for (int j = 0; j < numDays; j++) {
          cp.add(cp.imply(cp.eq(shifts_array[i][j], 3), cp.eq(evening_shifts_array[i][j], 1)));
        }
      }
      for (int j = 0; j < numDays; j++) {
        IloLinearNumExpr totalEveningsToday = cp.linearNumExpr();
        for (int i = 0; i < numEmployees; i++) {
          totalEveningsToday.addTerm(1, evening_shifts_array[i][j]);
        }
        cp.add(cp.ge(totalEveningsToday, minDemandDayShift[j][3]));
      }

      IloIntVar[][] off_shifts_array = new IloIntVar[numEmployees][numDays];
      for (int i = 0; i < numEmployees; i++) {
        for (int j = 0; j < numDays; j++) {
          off_shifts_array[i][j] = cp.intVar(0,1);
        }
      }
      for (int i = 0; i < numEmployees; i++) {
        for (int j = 0; j < numDays; j++) {
          cp.add(cp.imply(cp.eq(shifts_array[i][j], 0), cp.eq(off_shifts_array[i][j], 1)));
        }
      }
      for (int j = 0; j < numDays; j++) {
        IloLinearNumExpr totalOffsToday = cp.linearNumExpr();
        for (int i = 0; i < numEmployees; i++) {
          totalOffsToday.addTerm(1, off_shifts_array[i][j]);
        }
        cp.add(cp.ge(totalOffsToday, minDemandDayShift[j][0]));
      }

      for (int i = 0; i < numEmployees; i++) {
        // First four days all different
        //IloIntVar tmp = cp.intVar(0,0);
        //IloIntExpr totalNightShifts = cp.sum(tmp,tmp);
        //IloLinearNumExpr totalNightShifts = cp.linearNumExpr();
        IloIntVar[] firstFourDays = {shifts_array[i][0], shifts_array[i][1], shifts_array[i][2], shifts_array[i][3]};
        cp.add(cp.allDiff(firstFourDays));

        for (int j = 0; j < numDays; j++) {
          if (j+1 < numDays) {
            // Constraint that no two days in a row can be night shifts
            cp.add(cp.imply(cp.eq(shifts_array[i][j], 1), cp.neq(shifts_array[i][j+1], 1)));
            // if (shifts_array[i][j] == 1) {
            //   totalNightShifts.addTerm(1,shifts_array[i][j]);//cp.sum(totalNightShifts, 1);
            // }
          }
        }
        // cp.add(cp.le(totalNightShifts, maxTotalNightShift));

      }

      IloLinearIntExpr[][] workSum_array = new IloLinearIntExpr[numEmployees][numWeeks];

      IloIntVar[][][] times_array = new IloIntVar[numEmployees][numDays][2];
      for (int i = 0; i < numEmployees; i++) {

        for (int j = 0; j < numDays; j++) {
          // SOMETHING WITH -1
          times_array[i][j][0] = cp.intVar(-1,20);
          times_array[i][j][1] = cp.intVar(-1,24);

        }
      }
      System.out.println("MAX WEEKLY WORK " + maxWeeklyWork);
      System.out.println("MIN WEEKLY WORK " + minWeeklyWork);
      for (int i = 0; i < numEmployees; i++) {
        for(int week = 0; week < numWeeks; week++){
          workSum_array[i][week] = cp.linearIntExpr();
          // IloLinearIntExpr totalHours = cp.linearIntExpr();

          for (int j = 0; j < 7; j++) {

            cp.add(cp.le(cp.diff(times_array[i][7*week+j][1], times_array[i][7*week+j][0]), maxDailyWork));
            // Only if this is not an off shift does this constaint apply
            cp.add(cp.imply(cp.neq(shifts_array[i][7*week+j], 0), cp.ge(cp.diff(times_array[i][7*week+j][1], times_array[i][7*week+j][0]), minConsecutiveWork)));

            workSum_array[i][week].addTerm(1, times_array[i][7*week+j][1]);
            workSum_array[i][week].addTerm(-1, times_array[i][7*week+j][0]);


            //totalHours.addTerm(1, times_array[i][j][1]);
            //totalHours.addTerm(-1, times_array[i][j][0]);

            //workSum.addTerm(1, cp.diff(times_array[i][j][1], times_array[i][j][0]));
            //totalHours.addTerm(1, cp.diff(times_array[i][j][1], times_array[i][j][0]));

        }
        cp.add(cp.le(workSum_array[i][week], maxWeeklyWork));
        cp.add(cp.ge(workSum_array[i][week], minWeeklyWork));
        //cp.add(cp.ge(totalHours, minDailyOperation));
      }
    }

    for(int j = 0; j < numDays; j ++){
      IloLinearIntExpr totalHours = cp.linearIntExpr();
      for(int i = 0; i < numEmployees; i++){
        totalHours.addTerm(1, times_array[i][j][1]);
        totalHours.addTerm(-1, times_array[i][j][0]);
      }
      cp.add(cp.ge(totalHours, minDailyOperation));
    }

    // ATTEMPTING TO HANDLE THE -1
    for (int i = 0; i < numEmployees; i++) {
      for (int j = 0; j < numDays; j++) {
        cp.add(cp.imply( cp.eq(times_array[i][j][0], -1), cp.eq(shifts_array[i][j],0)));
        cp.add(cp.imply(cp.eq(times_array[i][j][1], -1), cp.eq(shifts_array[i][j],0)));
        // Constraint that if start is -1 end has to be -1 and vice versa
        // Problem is that this violates minConsecutiveWork constraint
        cp.add(cp.imply(cp.eq(times_array[i][j][1], -1), cp.eq(times_array[i][j][0], -1)));
        cp.add(cp.imply(cp.eq(times_array[i][j][0], -1), cp.eq(times_array[i][j][1], -1)));

        cp.add(cp.imply(cp.eq(shifts_array[i][j], 0), cp.eq(times_array[i][j][0], -1)));
        cp.add(cp.imply(cp.eq(shifts_array[i][j], 0), cp.eq(times_array[i][j][1],-1)));
      }
    }

      // Uncomment this: to set the solver output level if you wish
      // cp.setParameter(IloCP.IntParam.LogVerbosity, IloCP.ParameterValues.Quiet);
      if(cp.solve())
      {
        cp.printInformation();

        //String out = "";
        for(int i = 0; i < numEmployees; i++){
          String out = "";
          for(int j = 0; j < numDays; j++){
            out += cp.getValue(times_array[i][j][0]);
            out += " ";
            out += cp.getValue(times_array[i][j][1]);
            out += " ";
          }
          System.out.println(out);
          System.out.println("");
        }
        //System.out.println(out);
        //System.out.println("WORK SUM " + cp.getValue(workSum_array[0]));
        // Uncomment this: for poor man's Gantt Chart to display schedules
        // prettyPrint(numEmployees, numDays, beginED, endED);
      }
      else
      {
        System.out.println("No Solution found!");
        System.out.println("Number of fails: " + cp.getInfo(IloCP.IntInfo.NumberOfFails));
      }
    }
    catch(IloException e)
    {
      System.out.println("Error: " + e);
    }
  }

  // SK: technically speaking, the model with the global constaints
  // should result in fewer number of fails. In this case, the problem
  // is so simple that, the solver is able to re-transform the model
  // and replace inequalities with the global all different constrains.
  // Therefore, the results don't really differ
  void solveAustraliaGlobal()
  {
    String[] Colors = {"red", "green", "blue"};
    try
    {
      cp = new IloCP();
      IloIntVar WesternAustralia = cp.intVar(0, 3);
      IloIntVar NorthernTerritory = cp.intVar(0, 3);
      IloIntVar SouthAustralia = cp.intVar(0, 3);
      IloIntVar Queensland = cp.intVar(0, 3);
      IloIntVar NewSouthWales = cp.intVar(0, 3);
      IloIntVar Victoria = cp.intVar(0, 3);

      IloIntExpr[] clique1 = new IloIntExpr[3];
      clique1[0] = WesternAustralia;
      clique1[1] = NorthernTerritory;
      clique1[2] = SouthAustralia;

      IloIntExpr[] clique2 = new IloIntExpr[3];
      clique2[0] = Queensland;
      clique2[1] = NorthernTerritory;
      clique2[2] = SouthAustralia;

      IloIntExpr[] clique3 = new IloIntExpr[3];
      clique3[0] = Queensland;
      clique3[1] = NewSouthWales;
      clique3[2] = SouthAustralia;

      IloIntExpr[] clique4 = new IloIntExpr[3];
      clique4[0] = Queensland;
      clique4[1] = Victoria;
      clique4[2] = SouthAustralia;

      cp.add(cp.allDiff(clique1));
      cp.add(cp.allDiff(clique2));
      cp.add(cp.allDiff(clique3));
      cp.add(cp.allDiff(clique4));

	  cp.setParameter(IloCP.IntParam.Workers, 1);
      cp.setParameter(IloCP.DoubleParam.TimeLimit, 300);
	  cp.setParameter(IloCP.IntParam.SearchType, IloCP.ParameterValues.DepthFirst);

      if (cp.solve())
      {
         System.out.println();
         System.out.println( "WesternAustralia:    " + Colors[(int)cp.getValue(WesternAustralia)]);
         System.out.println( "NorthernTerritory:   " + Colors[(int)cp.getValue(NorthernTerritory)]);
         System.out.println( "SouthAustralia:      " + Colors[(int)cp.getValue(SouthAustralia)]);
         System.out.println( "Queensland:          " + Colors[(int)cp.getValue(Queensland)]);
         System.out.println( "NewSouthWales:       " + Colors[(int)cp.getValue(NewSouthWales)]);
         System.out.println( "Victoria:            " + Colors[(int)cp.getValue(Victoria)]);
      }
      else
      {
        System.out.println("No Solution found!");
      }
    } catch (IloException e)
    {
      System.out.println("Error: " + e);
    }
  }

  void solveAustraliaBinary()
  {
    String[] Colors = {"red", "green", "blue"};
    try
    {
      cp = new IloCP();
      IloIntVar WesternAustralia = cp.intVar(0, 3);
      IloIntVar NorthernTerritory = cp.intVar(0, 3);
      IloIntVar SouthAustralia = cp.intVar(0, 3);
      IloIntVar Queensland = cp.intVar(0, 3);
      IloIntVar NewSouthWales = cp.intVar(0, 3);
      IloIntVar Victoria = cp.intVar(0, 3);

      cp.add(cp.neq(WesternAustralia , NorthernTerritory));
      cp.add(cp.neq(WesternAustralia , SouthAustralia));
      cp.add(cp.neq(NorthernTerritory , SouthAustralia));
      cp.add(cp.neq(NorthernTerritory , Queensland));
      cp.add(cp.neq(SouthAustralia , Queensland));
      cp.add(cp.neq(SouthAustralia , NewSouthWales));
      cp.add(cp.neq(SouthAustralia , Victoria));
      cp.add(cp.neq(Queensland , NewSouthWales));
      cp.add(cp.neq(NewSouthWales , Victoria));

	  cp.setParameter(IloCP.IntParam.Workers, 1);
      cp.setParameter(IloCP.DoubleParam.TimeLimit, 300);
	  cp.setParameter(IloCP.IntParam.SearchType, IloCP.ParameterValues.DepthFirst);

      if (cp.solve())
      {
         System.out.println();
         System.out.println( "WesternAustralia:    " + Colors[(int)cp.getValue(WesternAustralia)]);
         System.out.println( "NorthernTerritory:   " + Colors[(int)cp.getValue(NorthernTerritory)]);
         System.out.println( "SouthAustralia:      " + Colors[(int)cp.getValue(SouthAustralia)]);
         System.out.println( "Queensland:          " + Colors[(int)cp.getValue(Queensland)]);
         System.out.println( "NewSouthWales:       " + Colors[(int)cp.getValue(NewSouthWales)]);
         System.out.println( "Victoria:            " + Colors[(int)cp.getValue(Victoria)]);
      }
      else
      {
        System.out.println("No Solution found!");
      }
    } catch (IloException e)
    {
      System.out.println("Error: " + e);
    }
  }

  void solveSendMoreMoney()
  {
    try
    {
      // CP Solver
      cp = new IloCP();

      // SEND MORE MONEY
      IloIntVar S = cp.intVar(1, 9);
      IloIntVar E = cp.intVar(0, 9);
      IloIntVar N = cp.intVar(0, 9);
      IloIntVar D = cp.intVar(0, 9);
      IloIntVar M = cp.intVar(1, 9);
      IloIntVar O = cp.intVar(0, 9);
      IloIntVar R = cp.intVar(0, 9);
      IloIntVar Y = cp.intVar(0, 9);

      IloIntVar[] vars = new IloIntVar[]{S, E, N, D, M, O, R, Y};
      cp.add(cp.allDiff(vars));

      //                1000 * S + 100 * E + 10 * N + D
      //              + 1000 * M + 100 * O + 10 * R + E
      //  = 10000 * M + 1000 * O + 100 * N + 10 * E + Y

      IloIntExpr SEND = cp.sum(cp.prod(1000, S), cp.sum(cp.prod(100, E), cp.sum(cp.prod(10, N), D)));
      IloIntExpr MORE   = cp.sum(cp.prod(1000, M), cp.sum(cp.prod(100, O), cp.sum(cp.prod(10,R), E)));
      IloIntExpr MONEY  = cp.sum(cp.prod(10000, M), cp.sum(cp.prod(1000, O), cp.sum(cp.prod(100, N), cp.sum(cp.prod(10,E), Y))));

      cp.add(cp.eq(MONEY, cp.sum(SEND, MORE)));

      // Solver parameters
      cp.setParameter(IloCP.IntParam.Workers, 1);
      cp.setParameter(IloCP.IntParam.SearchType, IloCP.ParameterValues.DepthFirst);
      if(cp.solve())
      {
        System.out.println("  " + cp.getValue(S) + " " + cp.getValue(E) + " " + cp.getValue(N) + " " + cp.getValue(D));
        System.out.println("  " + cp.getValue(M) + " " + cp.getValue(O) + " " + cp.getValue(R) + " " + cp.getValue(E));
        System.out.println(cp.getValue(M) + " " + cp.getValue(O) + " " + cp.getValue(N) + " " + cp.getValue(E) + " " + cp.getValue(Y));
      }
      else
      {
        System.out.println("No Solution!");
      }
    } catch (IloException e)
    {
      System.out.println("Error: " + e);
    }
  }

 /**
   * Poor man's Gantt chart.
   * author: skadiogl
   *
   * Displays the employee schedules on the command line.
   * Each row corresponds to a single employee.
   * A "+" refers to a working hour and "." means no work
   * The shifts are separated with a "|"
   * The days are separated with "||"
   *
   * This might help you analyze your solutions.
   *
   * @param numEmployees the number of employees
   * @param numDays the number of days
   * @param beginED int[e][d] the hour employee e begins work on day d, -1 if not working
   * @param endED   int[e][d] the hour employee e ends work on day d, -1 if not working
   */
  void prettyPrint(int numEmployees, int numDays, int[][] beginED, int[][] endED)
  {
    for (int e = 0; e < numEmployees; e++)
    {
      System.out.print("E"+(e+1)+": ");
      if(e < 9) System.out.print(" ");
      for (int d = 0; d < numDays; d++)
      {
        for(int i=0; i < numIntervalsInDay; i++)
        {
          if(i%8==0)System.out.print("|");
          if (beginED[e][d] != endED[e][d] && i >= beginED[e][d] && i < endED[e][d]) System.out.print("+");
          else  System.out.print(".");
        }
        System.out.print("|");
      }
      System.out.println(" ");
    }
  }

}
