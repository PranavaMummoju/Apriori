/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package apriori;

/**
 *
 * @author Pranava
 */
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Scanner;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

class AssociationRule<I> {

    private final Set<I> antecedent = new HashSet<>();
    private final Set<I> consequent = new HashSet<>();
    private double confidence;

    public AssociationRule(Set<I> antecedent, 
                           Set<I> consequent, 
                           double confidence) {
        Objects.requireNonNull(antecedent, "The rule antecedent is null.");
        Objects.requireNonNull(consequent, "The rule consequent is null.");
        this.antecedent.addAll(antecedent);
        this.consequent.addAll(consequent);
        this.confidence = confidence;
    }

    public AssociationRule(Set<I> antecedent, Set<I> consequent) {
        this(antecedent, consequent, Double.NaN);
    }

    public Set<I> getAntecedent() {
        return Collections.<I>unmodifiableSet(antecedent);
    }

    public Set<I> getConsequent() {
        return Collections.<I>unmodifiableSet(consequent);
    }

    public double getConfidence() {
        return confidence;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append(Arrays.toString(antecedent.toArray()));
        sb.append(" -> ");
        sb.append(Arrays.toString(consequent.toArray()));
        sb.append(": ");
        sb.append(confidence);

        return sb.toString();
    }

    @Override
    public int hashCode() {
        return antecedent.hashCode() ^ consequent.hashCode();
    }

    @Override
    public boolean equals(Object obj) {
        AssociationRule<I> other = (AssociationRule<I>) obj;

        return antecedent.equals(other.antecedent) &&
               consequent.equals(other.consequent);
    }
}

class FrequentItemsetData<I> {

    private final List<Set<I>> frequentItemsetList;
    private final Map<Set<I>, Integer> supportCountMap;
    private final double minimumSupport;
    private final int numberOfTransactions;

    FrequentItemsetData(List<Set<I>> frequentItemsetList,
                        Map<Set<I>, Integer> supportCountMap,
                        double minimumSupport,
                        int transactionNumber) {
        this.frequentItemsetList = frequentItemsetList;
        this.supportCountMap = supportCountMap;
        this.minimumSupport = minimumSupport;
        this.numberOfTransactions = transactionNumber;
    }

    public List<Set<I>> getFrequentItemsetList() {
        return frequentItemsetList;
    }

    public Map<Set<I>, Integer> getSupportCountMap() {
        return supportCountMap;
    }

    public double getMinimumSupport() {
        return minimumSupport;
    }

    public int getTransactionNumber() {
        return numberOfTransactions;
    }

    public double getSupport(Set<I> itemset) {
        return 1.0 * supportCountMap.get(itemset) / numberOfTransactions;
    }
}

class AssociationRuleGenerator<I> {

    public List<AssociationRule<I>> 
        mineAssociationRules(FrequentItemsetData<I> data,
                             double minimumConfidence) {
        Objects.requireNonNull(data, "The frequent itemset data is null.");
        checkMinimumConfidence(minimumConfidence);

        Set<AssociationRule<I>> resultSet = new HashSet<>();

        for (Set<I> itemset : data.getFrequentItemsetList()) {
            if (itemset.size() < 2) {
                // Any association rule requires at least one item in the 
                // antecedent, and at least one item in the consequent. An
                // itemset containing less than two items cannot satisfy this
                // requirement; skip it.
                continue;
            }

            // Generate the basic association rules out of current itemset.
            // An association rule is basic iff its consequent contains only one
            // item.
            Set<AssociationRule<I>> basicAssociationRuleSet = 
                    generateAllBasicAssociationRules(itemset, data);

            generateAssociationRules(itemset,
                                     basicAssociationRuleSet,
                                     data,
                                     minimumConfidence,
                                     resultSet);
        }

        List<AssociationRule<I>> ret = new ArrayList<>(resultSet);

        return resultSet.stream().sorted((a1, a2) -> Double.compare(a2.getConfidence(), a1.getConfidence())).collect(Collectors.toList());
    }

    private void generateAssociationRules(Set<I> itemset,
                                          Set<AssociationRule<I>> ruleSet,
                                          FrequentItemsetData<I> data,
                                          double minimumConfidence,
                                          Set<AssociationRule<I>> collector) {
        if (ruleSet.isEmpty()) {
            return;
        }

        // The size of the itemset.
        int k = itemset.size(); 
        // The size of the consequent of the input rules.
        int m = ruleSet.iterator().next().getConsequent().size();

        // Test whether we can pull one more item from the antecedent to 
        // consequent.
        if (k > m + 1) {
            Set<AssociationRule<I>> nextRules =
                    moveOneItemToConsequents(itemset, ruleSet, data);

            Iterator<AssociationRule<I>> iterator = nextRules.iterator();

            while (iterator.hasNext()) {
                AssociationRule<I> rule = iterator.next();

                if (rule.getConfidence() >= minimumConfidence) {
                    collector.add(rule);
                } else {
                    iterator.remove();
                }
            }

            generateAssociationRules(itemset,
                                     nextRules,
                                     data,
                                     minimumConfidence,
                                     collector);
        }
    }

    private Set<AssociationRule<I>> 
        moveOneItemToConsequents(Set<I> itemset, 
                                 Set<AssociationRule<I>> ruleSet,
                                 FrequentItemsetData<I> data) {
        Set<AssociationRule<I>> output = new HashSet<>();
        Set<I> antecedent = new HashSet<>();
        Set<I> consequent = new HashSet<>();
        double itemsetSupportCount = data.getSupportCountMap().get(itemset);

        // For each rule ...
        for (AssociationRule<I> rule : ruleSet) {
            antecedent.clear();
            consequent.clear();
            antecedent.addAll(rule.getAntecedent());
            consequent.addAll(rule.getConsequent());

            // ... move one item from its antecedent to its consequnt.
            for (I item : rule.getAntecedent()) {
                antecedent.remove(item);
                consequent.add(item);

                int antecedentSupportCount = data.getSupportCountMap()
                                                 .get(antecedent);
                AssociationRule<I> newRule = 
                        new AssociationRule<>(
                                antecedent,
                                consequent,
                                itemsetSupportCount / antecedentSupportCount);

                output.add(newRule);

                antecedent.add(item);
                consequent.remove(item);
            }
        }

        return output;
    }

    private Set<AssociationRule<I>> 
        generateAllBasicAssociationRules(Set<I> itemset,
                                         FrequentItemsetData<I> data) {
        Set<AssociationRule<I>> basicAssociationRuleSet =
                new HashSet<>(itemset.size());

        Set<I> antecedent = new HashSet<>(itemset);
        Set<I> consequent = new HashSet<>(1);

        for (I item : itemset) {
            antecedent.remove(item);
            consequent.add(item);

            int itemsetSupportCount = data.getSupportCountMap().get(itemset);
            int antecedentSupportCount = data.getSupportCountMap()
                                             .get(antecedent);

            double confidence = 1.0 * itemsetSupportCount 
                                    / antecedentSupportCount;

            basicAssociationRuleSet.add(new AssociationRule(antecedent, 
                                                            consequent,
                                                            confidence));
            antecedent.add(item);
            consequent.remove(item);
        }

        return basicAssociationRuleSet;
    }

    private void checkMinimumConfidence(double minimumConfidence) {
        if (Double.isNaN(minimumConfidence)) {
            throw new IllegalArgumentException(
                    "The input minimum confidence is NaN.");
        }

        if (minimumConfidence < 0.0) {
            throw new IllegalArgumentException(
                    "The input minimum confidence is negative: " + 
                    minimumConfidence + ". " +
                    "Must be at least zero.");
        }

        if (minimumConfidence > 1.0) {
            throw new IllegalArgumentException(
                    "The input minimum confidence is too large: " +
                    minimumConfidence + ". " +
                    "Must be at most 1.");
        }
    }
}

class AprioriFrequentItemsetGenerator<I> {

    public FrequentItemsetData<I> generate(List<Set<I>> transactionList, 
                                           double minimumSupport) {
        Objects.requireNonNull(transactionList, "The itemset list is empty.");
        checkSupport(minimumSupport);

        if (transactionList.isEmpty()) {
            return null;
        }

        // Maps each itemset to its support count. Support count is simply the 
        // number of times an itemset appeares in the transaction list.
        Map<Set<I>, Integer> supportCountMap = new HashMap<>();

        // Get the list of 1-itemsets that are frequent.
        List<Set<I>> frequentItemList = findFrequentItems(transactionList,
                                                          supportCountMap,
                                                          minimumSupport);


        // Maps each 'k' to the list of frequent k-itemsets. 
        Map<Integer, List<Set<I>>> map = new HashMap<>();
        map.put(1, frequentItemList);

        // 'k' denotes the cardinality of itemsets processed at each iteration
        // of the following loop.
        int k = 1;

        do {
            ++k;

            // First generate the candidates.
            List<Set<I>> candidateList = 
                    generateCandidates(map.get(k - 1));

            for (Set<I> transaction : transactionList) {
                List<Set<I>> candidateList2 = subset(candidateList,
                                                     transaction);

                for (Set<I> itemset : candidateList2) {
                    supportCountMap.put(itemset,
                                        supportCountMap.getOrDefault(itemset, 
                                                                     0) + 1);
                }
            }

            map.put(k, getNextItemsets(candidateList,
                                       supportCountMap, 
                                       minimumSupport, 
                                       transactionList.size()));

        } while (!map.get(k).isEmpty());

        return new FrequentItemsetData<>(extractFrequentItemsets(map),
                                         supportCountMap,
                                         minimumSupport,
                                         transactionList.size());
    }

    private List<Set<I>>
        extractFrequentItemsets(Map<Integer, List<Set<I>>> map) {
        List<Set<I>> ret = new ArrayList<>();

        for (List<Set<I>> itemsetList : map.values()) {
            ret.addAll(itemsetList);
        }

        return ret;
    }

    private List<Set<I>> getNextItemsets(List<Set<I>> candidateList,
                                         Map<Set<I>, Integer> supportCountMap,
                                         double minimumSupport,
                                         int transactions) {
        List<Set<I>> ret = new ArrayList<>(candidateList.size());

        for (Set<I> itemset : candidateList) {
            if (supportCountMap.containsKey(itemset)) {
                int supportCount = supportCountMap.get(itemset);
                double support = 1.0 * supportCount / transactions;

                if (support >= minimumSupport) {
                    ret.add(itemset);
                }
            }
        }

        return ret;
    }

    private List<Set<I>> subset(List<Set<I>> candidateList, 
                                Set<I> transaction) {
        List<Set<I>> ret = new ArrayList<>(candidateList.size());

        for (Set<I> candidate : candidateList) {
            if (transaction.containsAll(candidate)) {
                ret.add(candidate);
            }
        }

        return ret;
    }

    private List<Set<I>> generateCandidates(List<Set<I>> itemsetList) {
        List<List<I>> list = new ArrayList<>(itemsetList.size());

        for (Set<I> itemset : itemsetList) {
            List<I> l = new ArrayList<>(itemset);
            Collections.<I>sort(l, ITEM_COMPARATOR);
            list.add(l);
        }

        int listSize = list.size();

        List<Set<I>> ret = new ArrayList<>(listSize);

        for (int i = 0; i < listSize; ++i) {
            for (int j = i + 1; j < listSize; ++j) {
                Set<I> candidate = tryMergeItemsets(list.get(i), list.get(j));

                if (candidate != null) {
                    ret.add(candidate);
                }
            }
        }

        return ret;
    }

    private Set<I> tryMergeItemsets(List<I> itemset1, List<I> itemset2) {
        int length = itemset1.size();

        for (int i = 0; i < length - 1; ++i) {
            if (!itemset1.get(i).equals(itemset2.get(i))) {
                return null;
            }
        }

        if (itemset1.get(length - 1).equals(itemset2.get(length - 1))) {
            return null;
        }

        Set<I> ret = new HashSet<>(length + 1);

        for (int i = 0; i < length - 1; ++i) {
            ret.add(itemset1.get(i));
        }

        ret.add(itemset1.get(length - 1));
        ret.add(itemset2.get(length - 1));
        return ret;
    }

    private static final Comparator ITEM_COMPARATOR = new Comparator() {

        @Override
        public int compare(Object o1, Object o2) {
            return ((Comparable) o1).compareTo(o2);
        }

    };

    private List<Set<I>> findFrequentItems(List<Set<I>> itemsetList,
                                           Map<Set<I>, Integer> supportCountMap,
                                           double minimumSupport) {
        Map<I, Integer> map = new HashMap<>();

        // Count the support counts of each item.
        for (Set<I> itemset : itemsetList) {
            for (I item : itemset) {
                Set<I> tmp = new HashSet<>(1);
                tmp.add(item);

                supportCountMap.put(tmp, 
                                    supportCountMap.getOrDefault(tmp, 0) + 1);

                map.put(item, map.getOrDefault(item, 0) + 1);
            }
        }

        List<Set<I>> frequentItemsetList = new ArrayList<>();

        for (Map.Entry<I, Integer> entry : map.entrySet()) {
            if (1.0 * entry.getValue() / itemsetList.size() >= minimumSupport) {
                Set<I> itemset = new HashSet<>(1);
                itemset.add(entry.getKey());
                frequentItemsetList.add(itemset);
            }
        }

        return frequentItemsetList;
    }

    private void checkSupport(double support) {
        if (Double.isNaN(support)) {
            throw new IllegalArgumentException("The input support is NaN.");
        }

        if (support > 1.0) {
            throw new IllegalArgumentException(
                    "The input support is too large: " + support + ", " +
                    "should be at most 1.0");
        }

        if (support < 0.0) {
            throw new IllegalArgumentException(
                    "The input support is too small: " + support + ", " +
                    "should be at least 0.0");
        }
    }
}

public class Apriori {

    public static void main(String[] args) throws IOException {
        demo();
    }

    private static void demo() throws IOException {
        List<Set<String>> itemsetList = new ArrayList<>();
        AprioriFrequentItemsetGenerator<String> generator = new AprioriFrequentItemsetGenerator<>();
        String filename = "itemsets.txt";
        Scanner sc = new Scanner(System.in);
        System.out.print("Enter the absolute path of input file: ");
        filename = sc.nextLine();
        System.out.print("Enter the absolute path for output file to be created: ");
        String outfilename = sc.nextLine();
        File file = new File(outfilename);
        file.getParentFile().mkdirs();
        PrintWriter pw = new PrintWriter(file);
        String line;
        float minConf, minSup;
        System.out.print("Enter minimum Support: ");
        minSup = sc.nextFloat();
        System.out.print("Enter minimum Confidence: ");
        minConf = sc.nextFloat();
        FileReader fr = new FileReader(filename);
	BufferedReader br = new BufferedReader(fr);
	FileWriter fw = new FileWriter("apriori_Output.txt");   //Output written to this file
	BufferedWriter bw = new BufferedWriter(fw);
        while((line = br.readLine()) != null) {
            line = line.trim();
            String arr[] = line.split(Pattern.quote(" "));
            HashSet<String> asd = new HashSet<String>();
            for(String s : arr) {
                
                asd.add(s);
            }
            //System.out.println(asd);
            itemsetList.add(asd);
	}

        long startTime = System.nanoTime();
        FrequentItemsetData<String> data = generator.generate(itemsetList, minSup); //Support set here
        long endTime = System.nanoTime();

        int i = 1;

        //System.out.println("--- Frequent itemsets ---");
        pw.println("<------- Frequent itemsets ------->");    
        
        for (Set<String> itemset : data.getFrequentItemsetList()) {
            pw.printf("%2d: %9s, support: %1.1f\n", i++, itemset, data.getSupport(itemset));
        }

        System.out.printf("Mined frequent itemset in %d milliseconds.\n", 
                          (endTime - startTime) / 1_000_000);

        startTime = System.nanoTime();
        List<AssociationRule<String>> associationRuleList = 
                new AssociationRuleGenerator<String>()
                        .mineAssociationRules(data, minConf); //Confidence set here
        endTime = System.nanoTime();

        i = 1;

        /*System.out.println();
        System.out.println("--- Association rules ---");*/
        pw.println();
        pw.println("<------- Association rules ------->");

        for (AssociationRule<String> rule : associationRuleList) {
            pw.printf("%2d: %s\n", i++, rule);
        }
        
        System.out.printf("Mined association rules in %d milliseconds.\n",
                          (endTime - startTime) / 1_000_000);
        pw.flush();
        pw.close();
    }
}