//package cmu.arktweetnlp;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.io.File;
import java.io.FileInputStream;
import java.util.regex.*;
import java.util.Arrays;
import java.util.List;
import java.util.ArrayList;
import java.util.Comparator;

import org.apache.commons.lang.StringEscapeUtils;

/**
 * Twokenize -- a tokenizer designed for Twitter text in English and some other European languages.
 * This is the Java version. If you want the old Python version, see: http://github.com/brendano/tweetmotif
 * 
 * This tokenizer code has gone through a long history:
 *
 * (1) Brendan O'Connor wrote original version in Python, http://github.com/brendano/tweetmotif
 *        TweetMotif: Exploratory Search and Topic Summarization for Twitter.
 *        Brendan O'Connor, Michel Krieger, and David Ahn.
 *        ICWSM-2010 (demo track), http://brenocon.com/oconnor_krieger_ahn.icwsm2010.tweetmotif.pdf
 * (2a) Kevin Gimpel and Daniel Mills modified it for POS tagging for the CMU ARK Twitter POS Tagger
 * (2b) Jason Baldridge and David Snyder ported it to Scala
 * (3) Brendan bugfixed the Scala port and merged with POS-specific changes
 *     for the CMU ARK Twitter POS Tagger  
 * (4) Tobi Owoputi ported it back to Java and added many improvements (2012-06)
 * (5) Sebastian Mielke made it unicode-aware (2016-05) and taught it to segment tweets for translation (2016-06)
 * 
 * Original home is http://github.com/brendano/ark-tweet-nlp and http://www.ark.cs.cmu.edu/TweetNLP
 *
 * There have been at least 2 other Java ports, but they are not in the lineage for the code here.
 */
public class Twokenize {
    static Pattern Contractions = Pattern.compile("(?i)(\\w+)(n['’′]t|['’′]ve|['’′]ll|['’′]d|['’′]re|['’′]s|['’′]m)$", Pattern.UNICODE_CHARACTER_CLASS);
    static Pattern Whitespace = Pattern.compile("[\\s\\p{Zs}]+", Pattern.UNICODE_CHARACTER_CLASS);

    static String punctChars = "['\"“”‘’.?!…,:;]"; 
    //static String punctSeq   = punctChars+"+";	//'anthem'. => ' anthem '.
    static String punctSeq   = "['\"“”‘’]+|[.?!,…]+|[:;]+";	//'anthem'. => ' anthem ' .
    static String entity     = "&(?:amp|lt|gt|quot);";
    //  URLs

    // BTO 2012-06: everyone thinks the daringfireball regex should be better, but they're wrong.
    // If you actually empirically test it the results are bad.
    // Please see https://github.com/brendano/ark-tweet-nlp/pull/9

    static String urlStart1  = "(?:https?://|\\bwww\\.)";
    static String commonTLDs = "(?:com|org|edu|gov|net|mil|aero|asia|biz|cat|coop|info|int|jobs|mobi|museum|name|pro|tel|travel|xxx)";
    static String ccTLDs	 = "(?:ac|ad|ae|af|ag|ai|al|am|an|ao|aq|ar|as|at|au|aw|ax|az|ba|bb|bd|be|bf|bg|bh|bi|bj|bm|bn|bo|br|bs|bt|" +
    "bv|bw|by|bz|ca|cc|cd|cf|cg|ch|ci|ck|cl|cm|cn|co|cr|cs|cu|cv|cx|cy|cz|dd|de|dj|dk|dm|do|dz|ec|ee|eg|eh|" +
    "er|es|et|eu|fi|fj|fk|fm|fo|fr|ga|gb|gd|ge|gf|gg|gh|gi|gl|gm|gn|gp|gq|gr|gs|gt|gu|gw|gy|hk|hm|hn|hr|ht|" +
    "hu|id|ie|il|im|in|io|iq|ir|is|it|je|jm|jo|jp|ke|kg|kh|ki|km|kn|kp|kr|kw|ky|kz|la|lb|lc|li|lk|lr|ls|lt|" +
    "lu|lv|ly|ma|mc|md|me|mg|mh|mk|ml|mm|mn|mo|mp|mq|mr|ms|mt|mu|mv|mw|mx|my|mz|na|nc|ne|nf|ng|ni|nl|no|np|" +
    "nr|nu|nz|om|pa|pe|pf|pg|ph|pk|pl|pm|pn|pr|ps|pt|pw|py|qa|re|ro|rs|ru|rw|sa|sb|sc|sd|se|sg|sh|si|sj|sk|" +
    "sl|sm|sn|so|sr|ss|st|su|sv|sy|sz|tc|td|tf|tg|th|tj|tk|tl|tm|tn|to|tp|tr|tt|tv|tw|tz|ua|ug|uk|us|uy|uz|" +
    "va|vc|ve|vg|vi|vn|vu|wf|ws|ye|yt|za|zm|zw)";	//TODO: remove obscure country domains?
    static String urlStart2  = "\\b(?:[A-Za-z\\d-])+(?:\\.[A-Za-z0-9]+){0,3}\\." + "(?:"+commonTLDs+"|"+ccTLDs+")"+"(?:\\."+ccTLDs+")?(?=\\W|$)";
    static String urlBody    = "(?:[^\\.\\s<>][^\\s<>]*?)?";
    static String urlExtraCrapBeforeEnd = "(?:"+punctChars+"|"+entity+")+?";
    static String urlEnd     = "(?:\\.\\.+|[<>]|\\s|$)";
    public static String url        = "(?:"+urlStart1+"|"+urlStart2+")"+urlBody+"(?=(?:"+urlExtraCrapBeforeEnd+")?"+urlEnd+")";


    // Numeric
    static String timeLike   = "\\d+(?::\\d+){1,2}";
    //static String numNum     = "\\d+\\.\\d+";
    static String numberWithCommas = "(?:(?<!\\d)\\d{1,3},)+?\\d{3}" + "(?=(?:[^,\\d]|$))";
    static String numComb	 = "\\p{Sc}?\\d+(?:\\.\\d+)+%?";

    // Abbreviations
    static String boundaryNotDot = "(?:$|\\s|[“\\u0022?!,:;]|" + entity + ")";
    static String aa1  = "(?:[A-Za-z]\\.){2,}(?=" + boundaryNotDot + ")";
    static String aa2  = "[^\\p{Alpha}](?:[\\p{Alpha}]\\.){1,}[\\p{Alpha}](?=" + boundaryNotDot + ")";
    static String standardAbbreviations = "\\b(?:[Mm]r|[Mm]rs|[Mm]s|[Dd]r|[Ss]r|[Jj]r|[Rr]ep|[Ss]en|[Ss]t)\\.";
    static String arbitraryAbbrev = "(?:" + aa1 +"|"+ aa2 + "|" + standardAbbreviations + ")";
    static String separators  = "(?:--+|―|—|~|–|=)";
    static String decorations = "(?:[♫♪]+|[★☆]+|[♥❤♡]+|[\\u2639-\\u263b]+|[\\ue001-\\uebbb]+)";
    static String thingsThatSplitWords = "[^\\s\\.,?\"]";
    static String embeddedApostrophe = thingsThatSplitWords+"+['’′]" + thingsThatSplitWords + "*";
    
    public static String OR(String... parts) {
        String prefix="(?:";
        StringBuilder sb = new StringBuilder();
        for (String s:parts){
            sb.append(prefix);
            prefix="|";
            sb.append(s);
        }
        sb.append(")");
        return sb.toString();
    }
    
    //  Emoticons
    static String normalEyes = "(?iu)[:=]"; // 8 and x are eyes but cause problems
    static String wink = "[;]";
    static String noseArea = "(?:|-|[^a-zA-Z0-9 ])"; // doesn't get :'-(
    static String happyMouths = "[D\\)\\]\\}]+";
    static String sadMouths = "[\\(\\[\\{]+";
    static String tongue = "[pPd3]+";
    static String otherMouths = "(?:[oO]+|[/\\\\]+|[vV]+|[Ss]+|[|]+)"; // remove forward slash if http://'s aren't cleaned

    // mouth repetition examples:
    // @aliciakeys Put it in a love song :-))
    // @hellocalyclops =))=))=)) Oh well

    static String bfLeft = "(♥|0|o|°|v|\\$|t|x|;|\\u0CA0|@|ʘ|•|・|◕|\\^|¬|\\*)";
    static String bfCenter = "(?:[\\.]|[_-]+)";
    static String bfRight = "\\2";
    static String s3 = "(?:--['\"])";
    static String s4 = "(?:<|&lt;|>|&gt;)[\\._-]+(?:<|&lt;|>|&gt;)";
    static String s5 = "(?:[.][_]+[.])";
    static String basicface = "(?:(?i)" +bfLeft+bfCenter+bfRight+ ")|" +s3+ "|" +s4+ "|" + s5;

    static String eeLeft = "[＼\\\\ƪԄ\\(（<>;ヽ\\-=~\\*]+";
    static String eeRight= "[\\-=\\);'\\u0022<>ʃ）/／ノﾉ丿╯σっµ~\\*]+";
    static String eeSymbol = "[^A-Za-z0-9\\s\\(\\)\\*:=-]";
    static String eastEmote = eeLeft + "(?:"+basicface+"|" +eeSymbol+")+" + eeRight;

    
    public static String emoticon = OR(
            // Standard version  :) :( :] :D :P
    		"(?:>|&gt;)?" + OR(normalEyes, wink) + OR(noseArea,"[Oo]") + 
            	OR(tongue+"(?=\\W|$|RT|rt|Rt)", otherMouths+"(?=\\W|$|RT|rt|Rt)", sadMouths, happyMouths),

            // reversed version (: D:  use positive lookbehind to remove "(word):"
            // because eyes on the right side is more ambiguous with the standard usage of : ;
            "(?<=(?: |^))" + OR(sadMouths,happyMouths,otherMouths) + noseArea + OR(normalEyes, wink) + "(?:<|&lt;)?",

            //inspired by http://en.wikipedia.org/wiki/User:Scapler/emoticons#East_Asian_style
            eastEmote.replaceFirst("2", "1"), basicface
            // iOS 'emoji' characters (some smileys, some symbols) [\ue001-\uebbb]  
            // TODO should try a big precompiled lexicon from Wikipedia, Dan Ramage told me (BTO) he does this
    );

    static String Hearts = "(?:<+/?3+)+"; //the other hearts are in decorations

    static String Arrows = "(?:<*[-―—=]*>+|<+[-―—=]*>*)|\\p{InArrows}+";

    // BTO 2011-06: restored Hashtag, AtMention protection (dropped in original scala port) because it fixes
    // "hello (#hashtag)" ==> "hello (#hashtag )"  WRONG
    // "hello (#hashtag)" ==> "hello ( #hashtag )"  RIGHT
    // "hello (@person)" ==> "hello (@person )"  WRONG
    // "hello (@person)" ==> "hello ( @person )"  RIGHT
    // ... Some sort of weird interaction with edgepunct I guess, because edgepunct 
    // has poor content-symbol detection.

    // This also gets #1 #40 which probably aren't hashtags .. but good as tokens.
    // If you want good hashtag identification, use a different regex.
    static String Hashtag = "#[\\w]+";  //optional: lookbehind for \b
    //optional: lookbehind for \b, max length 15
    static String AtMention = "[@＠][\\w]+"; 

    // I was worried this would conflict with at-mentions
    // but seems ok in sample of 5800: 7 changes all email fixes
    // http://www.regular-expressions.info/email.html
    static String Bound = "(?:\\W|^|$)";
    public static String Email = "(?<=" +Bound+ ")[\\w.%+-]+@[\\p{Alpha}0-9.-]+\\.[\\p{Alpha}]{2,4}(?=" +Bound+")";

    // We will be tokenizing using these regexps as delimiters
    // Additionally, these things are "protected", meaning they shouldn't be further split themselves.
    static Pattern Protected  = Pattern.compile(
            OR(
                    Hearts,
                    url,
                    Email,
                    timeLike,
                    //numNum,
                    numberWithCommas,
                    numComb,
                    emoticon,
                    Arrows,
                    entity,
                    punctSeq,
                    arbitraryAbbrev,
                    separators,
                    decorations,
                    embeddedApostrophe,
                    Hashtag,  
                    AtMention
            ), Pattern.UNICODE_CHARACTER_CLASS);

    // We don't want to define our segments using these
    static Pattern UnwantedProtected = Pattern.compile(
            OR(
                    url, // <- that one is really worth dicussing, but I actually prefer only matching the http/s:// stuff manually, naked URLs are more likely part of a sentence
                    Email,
                    timeLike,
                    numberWithCommas,
                    numComb,
                    entity,
                    punctSeq,
                    arbitraryAbbrev,
                    embeddedApostrophe,
                    Hashtag,  
                    AtMention
            ), Pattern.UNICODE_CHARACTER_CLASS);

    // Edge punctuation
    // Want: 'foo' => ' foo '
    // While also:   don't => don't
    // the first is considered "edge punctuation".
    // the second is word-internal punctuation -- don't want to mess with it.
    // BTO (2011-06): the edgepunct system seems to be the #1 source of problems these days.  
    // I remember it causing lots of trouble in the past as well.  Would be good to revisit or eliminate.

    // Note the 'smart quotes' (http://en.wikipedia.org/wiki/Smart_quotes)
    static String edgePunctChars    = "'\"“”‘’«»{}\\(\\)\\[\\]\\*&"; //add \\p{So}? (symbols)
    static String edgePunct    = "[" + edgePunctChars + "]";
    static String notEdgePunct = "[\\p{Alpha}0-9]"; // content characters
    static String offEdge = "(^|$|:|;|\\s|\\.|,)";  // colon here gets "(hello):" ==> "( hello ):"
    static Pattern EdgePunctLeft  = Pattern.compile(offEdge + "("+edgePunct+"+)("+notEdgePunct+")", Pattern.UNICODE_CHARACTER_CLASS);
    static Pattern EdgePunctRight = Pattern.compile("("+notEdgePunct+")("+edgePunct+"+)" + offEdge, Pattern.UNICODE_CHARACTER_CLASS);

    public static String splitEdgePunct (String input) {
        Matcher m1 = EdgePunctLeft.matcher(input);
        input = m1.replaceAll("$1$2 $3");
        m1 = EdgePunctRight.matcher(input);
        input = m1.replaceAll("$1 $2$3");
        return input;
    }
    
    private static class Pair<T1, T2> {
        public T1 first;
        public T2 second;
        public Pair(T1 x, T2 y) { first=x; second=y; }
    }

    private static Pair<Integer, Integer> growPair (Pair<Integer, Integer> p, String rawtext) {
      // grow left
      while (p.first > 0
              && Whitespace.matcher(rawtext.substring(p.first-1, p.first)).matches())
        p.first--;
      // grow right
      while (p.second < rawtext.length() - 1
              && Whitespace.matcher(rawtext.substring(p.second, p.second+1)).matches())
        p.second++;
      return p;
    }

    private static void growOverWhitespace (List<Pair<Integer,Integer>> allBadSpans, String rawtext) {
      for (Pair<Integer,Integer> p : allBadSpans) {
        growPair(p, rawtext);
      }
    }

    private static List<Pair<Integer,Integer>> simpleSegmentRaw (String rawtext) {
      List<Pair<Integer,Integer>> allBadSpans = new ArrayList<Pair<Integer,Integer>>();
      
      // Get all the useful Twokenizer matches
      Matcher matches = Protected.matcher(rawtext);
      while(matches.find()){
        if (matches.start() != matches.end()){ //unnecessary?
          String prot = rawtext.substring(matches.start(), matches.end());
          if(!UnwantedProtected.matcher(prot).matches())
            allBadSpans.add(new Pair<Integer, Integer>(matches.start(), matches.end()));
        }
      }
      
      // Okay, first my easy own protections:
      String easy_regex = OR("@[\\w]+:", "\\(?https?://[^\\s]+", ":'-?\\(+", "8D+", "[xX][dD]+", "\\.\\.+");
      matches = Pattern.compile(easy_regex, Pattern.UNICODE_CHARACTER_CLASS).matcher(rawtext);
      while(matches.find()){
        allBadSpans.add(new Pair<Integer, Integer>(matches.start(), matches.end()));
      }
      
      // Then the tricky sentence boundaries:
      String bound_regex = OR("(\\.)\\s+[\\p{Lu}\\p{Lt}]", "[!\\?]+");
      matches = Pattern.compile(bound_regex, Pattern.UNICODE_CHARACTER_CLASS).matcher(rawtext);
      // Here we have to shift the sep start one to the right to include it in
      // previous text!
      // Following punctuation can be part of the separator.
      while(matches.find()){
        String prot = rawtext.substring(matches.start(), matches.end());
        // I want the whole "!?" to be presented to the translator
        if(prot.length() >= 2 && prot.substring(0,2).equals("!?"))
          allBadSpans.add(new Pair<Integer, Integer>(matches.start() + 2, matches.end()));
        // The full stop captures the following capital letter, so draw end closer
        else if (prot.substring(0,1).equals("."))
          allBadSpans.add(new Pair<Integer, Integer>(matches.start() + 1, matches.end() - 1));
        // Otherwise really just exclude one punctuation mark from the separator
        else
          allBadSpans.add(new Pair<Integer, Integer>(matches.start() + 1, matches.end()));
      }
      
      // Now for my stupidly context-sensitive one, but they're only necessarily
      // context-sensitive in one direction, so by doing a forward and a
      // backward pass, we should catch 'em all!
      growOverWhitespace(allBadSpans, rawtext);
      
      // Backward pass (i.e. beforeSep or atEnd)
      String backward_regex = OR("[^\\s]*@" + OR(urlStart2, "\\w+"), "#[\\w]+");
      matches = Pattern.compile(backward_regex, Pattern.UNICODE_CHARACTER_CLASS).matcher(rawtext);
      // (going backwards is tricky, so cache all matches)
      List<Pair<Integer,Integer>> candidates = new ArrayList<>();
      while(matches.find()) {
        candidates.add(new Pair(matches.start(), matches.end()));
      }
      for(int i = candidates.size() - 1; i >= 0; i--) {
        Pair<Integer,Integer> p = candidates.get(i);
        boolean touching = false;
        if (p.second == rawtext.length())
          touching = true;
        else
          for(Pair<Integer,Integer> p_done : allBadSpans) {
            if(p.second >= p_done.first && p.first < p_done.first) {
              touching = true;
              break;
            }
          }
        if (touching)
          allBadSpans.add(growPair(p, rawtext));
      }
      // Forward pass (i.e. afterSep or atStart)
      String forward_regex = OR("[^\\s]*@" + OR(urlStart2, "\\w+"));
      matches = Pattern.compile(forward_regex, Pattern.UNICODE_CHARACTER_CLASS).matcher(rawtext);
      while(matches.find()){
        boolean touching = false;
        if (matches.start() == 0)
          touching = true;
        else
          for(Pair<Integer,Integer> p : allBadSpans) {
            if(matches.start() <= p.second && matches.end() > p.second) {
              touching = true;
              break;
            }
          }
        if (touching)
          allBadSpans.add(growPair(new Pair<Integer, Integer>(matches.start(), matches.end()), rawtext));
      }
      
      // Time for the union of all spans to get good and bad lists!
      // ... sort for the joining (next)
      allBadSpans.sort(new Comparator<Pair<Integer, Integer>>() {
        @Override
        public int compare(Pair<Integer, Integer> o1, Pair<Integer, Integer> o2) {
          if(o1.first != o2.first)
            return o1.first.compareTo(o2.first);
          else
            return o1.second.compareTo(o2.second);
        }
      });
      
      // ... join adjacent sep ranges
      int i = 0;
      while (i < allBadSpans.size() - 1) {
        if(allBadSpans.get(i).second >= allBadSpans.get(i+1).first) {
          allBadSpans.get(i).second = allBadSpans.get(i+1).second;
          allBadSpans.remove(i+1);
        } else {
          i++;
        }
      }
      
      return allBadSpans;
    }

    public static String simpleSegment (String rawtext_unsqueezed, String tokenized) {
      StringBuilder segInstr = new StringBuilder();
      String rawtext = squeezeWhitespace(rawtext_unsqueezed);
      List<Pair<Integer,Integer>> rawSegments = simpleSegmentRaw(rawtext);
      
      // Idea: we thread our way through both strings,
      // inserting "\ntext%" and "\nsep%" into the tokenized string
      // whenever we begin/end a span in the raw string, i.e. change state
      
      List<Integer> stateChangeIndices = new ArrayList<Integer>();
      for(Pair<Integer,Integer> p : rawSegments){
          stateChangeIndices.add(p.first);
          stateChangeIndices.add(p.second);
      }
      stateChangeIndices.add(rawtext.length());
      
      int iRaw = 0, iTok = 0;
      boolean isSep = false;
      boolean first = true;
      for(int iSC : stateChangeIndices) {
        if(iRaw == rawtext.length())
          break;
        if(first && stateChangeIndices.get(0) == 0) {
          first = false;
          isSep = !isSep;
          continue;
        } else
          first = false;
        
        segInstr.append(isSep ? "sep\t" : "text\t");
        boolean afterFirstNonSpace = false;
        while(iRaw < iSC) {
          char cTok = tokenized.charAt(iTok);
          char cRaw = rawtext.charAt(iRaw);
          String tok3 = (iTok < tokenized.length() - 2) ?
                          tokenized.substring(iTok, iTok+3) :
                        (iTok < tokenized.length() - 1) ?
                          tokenized.substring(iTok, iTok+2) :
                        "XX"; // won't match any of the >2 char cases.
          String raw3 = (iRaw < rawtext.length() - 2) ?
                          rawtext.substring(iRaw, iRaw+3) :
                        (iRaw < rawtext.length() - 1) ?
                          rawtext.substring(iRaw, iRaw+2) :
                        "XX"; // won't match any of the >2 char cases.
          if(cTok == cRaw
              || cTok == '“' && (cRaw == '"' || cRaw == '«' || cRaw == '”')
              || cTok == '”' && (cRaw == '"' || cRaw == '»' || cRaw == '“')
              ) {
            segInstr.append(cTok);
            iRaw++;
            iTok++;
            afterFirstNonSpace = true;
          } else if ((cTok == '“' || cTok == '”')
                    && raw3.substring(0,2).equals("''")) {
            segInstr.append(cTok);
            iRaw += 2;
            iTok++;
            afterFirstNonSpace = true;
          } else if (tok3.substring(0,2).equals("--")
                    && (cRaw == '–' || cRaw == '—')) {
            segInstr.append("--");
            iRaw++;
            iTok += 2;
            afterFirstNonSpace = true;
          } else if ((cTok == '…') && raw3.equals("...")) {
            segInstr.append(cTok);
            iRaw += 3;
            iTok++;
            afterFirstNonSpace = true;
          } else if (tok3.equals("...") && (cRaw == '…')) {
            segInstr.append("...");
            iRaw++;
            iTok += 3;
            afterFirstNonSpace = true;
          } else if (cTok == ' ') {
            if(!isSep && afterFirstNonSpace)
              segInstr.append(' ');
            iTok++;
          } else {
            throw new RuntimeException("Unsure about cTok '"+cTok+"' and cRaw '"+cRaw+"'");
          }
        }
        segInstr.append("\n");
        isSep = !isSep;
      }
      
      return segInstr.toString();
    }

    // The main work of tokenizing a tweet.
    private static List<String> simpleTokenize (String text) {

        // Do the no-brainers first
        String splitPunctText = splitEdgePunct(text);

        int textLength = splitPunctText.length();
        
        // BTO: the logic here got quite convoluted via the Scala porting detour
        // It would be good to switch back to a nice simple procedural style like in the Python version
        // ... Scala is such a pain.  Never again.

        // Find the matches for subsequences that should be protected,
        // e.g. URLs, 1.0, U.N.K.L.E., 12:53
        Matcher matches = Protected.matcher(splitPunctText);
        //Storing as List[List[String]] to make zip easier later on 
        List<List<String>> bads = new ArrayList<List<String>>();	//linked list?
        List<Pair<Integer,Integer>> badSpans = new ArrayList<Pair<Integer,Integer>>();
        while(matches.find()){
            // The spans of the "bads" should not be split.
            if (matches.start() != matches.end()){ //unnecessary?
                List<String> bad = new ArrayList<String>(1);
                bad.add(splitPunctText.substring(matches.start(),matches.end()));
                bads.add(bad);
                badSpans.add(new Pair<Integer, Integer>(matches.start(),matches.end()));
            }
        }

        // Create a list of indices to create the "goods", which can be
        // split. We are taking "bad" spans like 
        //     List((2,5), (8,10)) 
        // to create 
        ///    List(0, 2, 5, 8, 10, 12)
        // where, e.g., "12" here would be the textLength
        // has an even length and no indices are the same
        List<Integer> indices = new ArrayList<Integer>(2+2*badSpans.size());
        indices.add(0);
        for(Pair<Integer,Integer> p:badSpans){
            indices.add(p.first);
            indices.add(p.second);
        }
        indices.add(textLength);

        // Group the indices and map them to their respective portion of the string
        List<List<String>> splitGoods = new ArrayList<List<String>>(indices.size()/2);
        for (int i=0; i<indices.size(); i+=2) {
            String goodstr = splitPunctText.substring(indices.get(i),indices.get(i+1));
            List<String> splitstr = Arrays.asList(goodstr.trim().split(" "));
            splitGoods.add(splitstr);
        }

        //  Reinterpolate the 'good' and 'bad' Lists, ensuring that
        //  additonal tokens from last good item get included
        List<String> zippedStr= new ArrayList<String>();
        int i;
        for(i=0; i < bads.size(); i++) {
            zippedStr = addAllnonempty(zippedStr,splitGoods.get(i));
            zippedStr = addAllnonempty(zippedStr,bads.get(i));
        }
        zippedStr = addAllnonempty(zippedStr,splitGoods.get(i));
        
        // BTO: our POS tagger wants "ur" and "you're" to both be one token.
        // Uncomment to get "you 're"
        /*ArrayList<String> splitStr = new ArrayList<String>(zippedStr.size());
        for(String tok:zippedStr)
        	splitStr.addAll(splitToken(tok));
        zippedStr=splitStr;*/
        
        return zippedStr;
    }  

    private static List<String> addAllnonempty(List<String> master, List<String> smaller){
        for (String s : smaller){
            String strim = s.trim();
            if (strim.length() > 0)
                master.add(strim);
        }
        return master;
    }
    /** "foo   bar " => "foo bar" */
    public static String squeezeWhitespace (String input){
        return Whitespace.matcher(input).replaceAll(" ").trim();
    }

    // Final pass tokenization based on special patterns
    private static List<String> splitToken (String token) {

        Matcher m = Contractions.matcher(token);
        if (m.find()){
        	String[] contract = {m.group(1), m.group(2)};
        	return Arrays.asList(contract);
        }
        String[] contract = {token};
        return Arrays.asList(contract);
    }

    /** Assume 'text' has no HTML escaping. **/
    public static List<String> tokenize(String text){
        return simpleTokenize(squeezeWhitespace(text));
    }


    /**
     * Twitter text comes HTML-escaped, so unescape it.
     * We also first unescape &amp;'s, in case the text has been buggily double-escaped.
     */
    public static String normalizeTextForTagger(String text) {
    	text = text.replaceAll("&amp;", "&");
    	text = StringEscapeUtils.unescapeHtml(text);
    	return text;
    }

    /**
     * This is intended for raw tweet text -- we do some HTML entity unescaping before running the tagger.
     * 
     * This function normalizes the input text BEFORE calling the tokenizer.
     * So the tokens you get back may not exactly correspond to
     * substrings of the original text.
     */
    public static List<String> tokenizeRawTweetText(String text) {
        List<String> tokens = tokenize(normalizeTextForTagger(text));
        return tokens;
    }

    /** Tokenizes tweet texts on standard input, tokenizations on standard output.  Input and output UTF-8. */
    public static void main(String[] args) throws IOException {
      PrintStream output = new PrintStream(System.out, true, "UTF-8");
      // Original tokenizer behavior
      if (args.length == 0) {
        BufferedReader input = new BufferedReader(new InputStreamReader(System.in,"UTF-8"));
        String line;
        while ( (line = input.readLine()) != null) {
          List<String> toks = tokenizeRawTweetText(line);
          for (int i=0; i<toks.size(); i++) {
            output.print(toks.get(i));
            if (i < toks.size()-1) {
              output.print(" ");
            }
          }
        }
        output.print("\n");
      }
      else if (args.length == 2) { // new segmentation behavior
        BufferedReader raw = new BufferedReader(new InputStreamReader(
          new FileInputStream(new File(args[0])), "UTF-8"));
        BufferedReader tok = new BufferedReader(new InputStreamReader(
          new FileInputStream(new File(args[1])), "UTF-8"));
        String rawline, tokline;
        while ( (rawline = raw.readLine()) != null
                && (tokline = tok.readLine()) != null) {
          output.println(simpleSegment(rawline, tokline));
        }
      }
      
      //System.err.println("\n\n" + simpleSegment("So http://some.one or what.hu/s at 13.00 or, you know... 13:00 \"his highness\" said xD 420.00€ and :))) $13.00 for 100% - no [: 100.01% - yeah #yolo! Okay, that :D was fun XD xddd anyway <3 look at http://what.me or (https://s.de) for de@post.de Germans admin@post.de :'( :'-( oh well... Time @someguy: to go @man. Bye. bye. Really!? @woman Well @man!!!!! @woman #hashtag #yolo...", ""));
      
      /*
      System.err.println("\n\n" + simpleSegment(
        "itthooon:) mekkora volt Ajka úristen:D nyomatták rendesen:D végig ott voltunk ahh durva élmény:Dennyi koncertet:D Köszii Apa<3:)",
        "itthooon : ) mekkora volt Ajka úristen:D nyomatták rendesen:D végig ott voltunk ahh durva élmény:Dennyi koncertet:D Köszii Apa < 3 : )"));
      System.err.println("\n\n" + simpleSegment(
        "hattttalmas őrület volt rábapatyon, istenek vagytok! :D irány ajka, 16.00-kor nyomjuk! jeaaah bóóój! #fb",
        "hattttalmas őrület volt rábapatyon , istenek vagytok ! :D irány ajka , 16.00 - kor nyomjuk ! jeaaah bóóój ! #fb"));
      System.err.println("\n\n" + simpleSegment(
        "abc:Ddef:D ghi :D jkl abc:Ddef:D ghi :D jkl abc:Ddef:D ghi :D jkl",
        "abc:Ddef:D ghi :D jk l a bc: Ddef: D ghi : D jk l a bc : D def : D ghi  : D jkl"));
      // */
    }
}
