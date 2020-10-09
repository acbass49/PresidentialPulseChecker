#   AUTHOR: ALEX BASS
#   LAST UPDATED: 9/19/2020 

#HERE IS WHATS HAPPENING IN THIS DOCUMENT...

#          - Load data from 538 polls
#          - Clean data
#          - Build a model predicting adjustments to be made (EX: house effects, methodology, etc)
#          - Adjust data according to model
#          - Generate probabilities according to latest polls
#          - Display probabilities on a map
#          - Simulate election using these probabilities
#          - Plot simulation using a waffle chart
#          - Update stored csv file daily
#          - Plot a line graph daily tracker

#-----------------------------------------------------#
##LOADING PACKAGES AND SETTING WD
#-----------------------------------------------------#
setwd("~/rProjects")
library(tidyverse)
library(showtext)
library(rvest)
library(xml2)
library(plm)
library(lmtest)
library(multiwayvcov)
library(lubridate)
library(plotly)
library(usmap)
library(waffle)
library(sjlabelled)

#-----------------------------------------------------#
##FUNCTIONS FOR ANALYSIS
#-----------------------------------------------------#
#adjusts percents according to data given
adjust_percent <- function(cdb, percent, label){
  if (!is.na(cdb[label])){
    new_percent <- percent - cdb[label]
    return(new_percent)
  }else{
    return(percent)
  }
}

#adjusts candidate fully according to pollster, methodology, and sampling population
adjust_candidate <- function(fd, tdb, bdb){
  cdb <- tdb
  if (fd[["answer"]]=="Biden")cdb <- bdb
  pct <- fd[["pct"]]
  #pct <- adjust_percent(cdb, pct, fd[["pollster"]])
  #pct <- adjust_percent(cdb, pct, fd[["meth"]])
  pct <- adjust_percent(cdb, pct, fd[["population"]])
  #if (fd[["fb"]]=="versus")pct <- adjust_percent(cdb, pct, fd[["state"]])
  fd[["pct"]] <- pct
  return(fd)
}

#weights survey so biden and trump together = 100%
weight_to_100 <- function(data){
  weight <- 100/sum(data[["pct"]])
  data <- data %>% filter(answer == "Trump")
  data[["pct"]] <- data[["pct"]]*weight
  return(data)
}

#performs 1-sample t-test on for trump generating win probability
one_sample_ttest <- function(data){
  data[["pct"]] <- as.numeric(data[["pct"]])/100
  SE <- sqrt(data[["pct"]]*(1-data[["pct"]])/data[["sample_size"]])
  z_score <- (data[["pct"]]-.5)/(SE)
  return(pnorm(z_score))
}

#returns averaged probability from the 5 latest polls
return_1_prob <- function(data){
  data <- split(data, data[["question_id"]])
  data <- lapply(data, weight_to_100)
  data <- matrix(sapply(data, one_sample_ttest), ncol =1)
  av_prob <- mean(data)
  return(av_prob)
}

#master function -  generate a state probability
generate_state_probability <- function(states, data, TC, BC){
  question_list <- unlist(c(
    data %>% 
      filter(state %in% c(states), !duplicated(question_id)) %>% 
      mutate(date = mdy(end_date)) %>% 
      arrange(desc(date)) %>% 
      slice_head(n=5) %>% 
      select(question_id)))
  state_data <- data %>% 
    filter(question_id %in% question_list, answer %in% c("Trump", "Biden"))
  state_list <- split(state_data, seq_len(nrow(state_data)))
  adjusted_state_data <- data.table::rbindlist(lapply(state_list, adjust_candidate, tdb = TC, bdb = BC))
  vector <- c(return_1_prob(adjusted_state_data))
  return(vector)
}

#simulate one state given probability
one_state <- function(data)ifelse(rbinom(1,1,as.numeric(data[["prob"]]))==1,as.numeric(data[["Votes"]]),0)

#simulate election given probabilities
generate_simulations <- function(data, repeat_number){
  z <- c()
  x <- c()
  y <- c()
  for(lars in 1:repeat_number){
    use <- split(data, seq_len(nrow(data)))
    use <- sapply(use, one_state)
    z <- c(z,sum(use))
    y <- 270 - z
    if(sum(use)>270){
      x <- c(x,"Trump")
    }else if(sum(use)==270){
      x <- c(x, "Tie")
    }else{
      x <- c(x, "Biden")
    }
    if(lars%%100==0)print(lars)
  }
  return_data <- as.data.frame(cbind(x,z,y))
  names(return_data) <- c("Winner", "Votes for Trump", "Margin")
  return(return_data)
}

#these 2 functions are if I want to double the SE
return_2_prob <- function(data){
  av_sample_size <- data %>% filter(!duplicated(question_id)) %>% summarise(mean = mean(sample_size))
  av_sample_size <- av_sample_size[1,1]
  data <- split(data, data[["question_id"]])
  data <- matrix(sapply(data, weight_to_100), ncol = 1)
  av_trump_pct <- mean(data)/100
  SE <- sqrt((av_trump_pct*(1-av_trump_pct))/av_sample_size)
  z_score <- (av_trump_pct-.5)/(SE*2)
  return(pnorm(z_score))
}

generate2_state_probability <- function(states, data, TC, BC){
  question_list <- unlist(c(
    data %>% 
      filter(state %in% c(states), !duplicated(question_id)) %>% 
      mutate(date = mdy(end_date)) %>% 
      arrange(desc(date)) %>% 
      slice_head(n=5) %>% 
      select(question_id)))
  state_data <- data %>% 
    filter(question_id %in% question_list, answer %in% c("Trump", "Biden"))
  state_list <- split(state_data, seq_len(nrow(state_data)))
  adjusted_state_data <- data.table::rbindlist(lapply(state_list, adjust_candidate, tdb = TC, bdb = BC))
  vector <- c(return_2_prob(adjusted_state_data))
  return(vector)
}

#-----------------------------------------------------#
##SETTING OPTIONS AND LOADING DATA
#-----------------------------------------------------#
#sets output to decimal instead of scientific notation
options(scipen = 999)

#reading latest polls from 538
TvB <- read.csv("https://projects.fivethirtyeight.com/polls-page/president_polls.csv")

#reading match region with state data
region <- read.csv("Resources/region_state_match.csv")

#reading 538 model data
model538 <- read.csv("https://projects.fivethirtyeight.com/2020-general-data/presidential_state_toplines_2020.csv")

#reading data with EC vote data
state_votes <- read.csv("Resources/electoral_votes_by_state.csv")

#list of states for easy conversion
states_list <- read.csv("Resources/state_list.csv")

#-----------------------------------------------------#
##DATA CLEANING AND FILTERING
#-----------------------------------------------------#
#Selecting relevant variables and filtering out non-state polls and low grade polls
new <- TvB %>% 
  select(question_id, answer, pct, pollster, pollster_id, fte_grade, end_date, methodology, state, population, 
         candidate_party, sample_size) %>% 
  filter(fte_grade %in% c("A+", "A", "A-", "A/B","B+", "B", "B-", "B/C"), state!="")

new$meth <- factor(new$methodology, 
                   levels = c("Live Phone", "Online", "Automated Phone", "IVR/Online", "IVR/Text",
                              "Live Phone/Online", "Live Phone/Online/Text", "Online/IVR", 
                              "Online/Text", "Text"),
                   labels = c("Live Phone", "Online", "Other", "IVR/Online", 
                              "IVR/Text", "Other", "Other", "IVR/Online",
                              "Other", "Other"))

new$meth <- relevel(new$meth, ref = "Other")


#creating unsure vs. no unsure and an unsure category
new <- new %>% 
  group_by(question_id) %>% 
  mutate(unsure = ifelse(sum(pct)>99, NA, 100-sum(pct)),
         third_option = ifelse(sum(pct)>99, "Two", "Three")) %>% 
  ungroup()

#Filtering out full ballot questions
drop_these <- c()
for (row in seq_along(1:nrow(new))){
  if (!(new$answer[row] %in% c("Trump", "Biden"))){
    drop_these <- c(drop_these, new$question_id[row])
  }
}

#filtering out non-ballot/full ballot questions
keep_these <- c()
for (row in seq_along(1:nrow(new))){
  if (!(new$answer[row] %in% c("Trump", "Biden", "Jorgensen", "Hawkins"))){
    keep_these <- c(keep_these, new$question_id[row])
  }
}

#data w/ full ballot questions
wFB <- new %>% 
  mutate(fb = ifelse(!(question_id %in% drop_these),"versus","fullBallot")) %>% 
  filter(!(question_id %in% keep_these))

#data w/out full ballot questions
TvB1<- new %>% 
  filter(!(question_id %in% drop_these))

#creating population factor variable
wFB$population <- factor(wFB$population, levels=c("lv", "rv", "a", "v"))

#generating models using latest data
trumplm <- plm(pct ~ meth + state + pollster + population + sample_size + 
                 third_option + fb, 
               data = wFB %>% filter(answer=="Trump"), model = "within", index = c("state"))

bidenlm <- plm(pct ~ meth + state + pollster + population + sample_size + 
                 third_option + fb, 
               data = wFB %>% filter(answer=="Biden"), model = "within", index = c("state"))

TRUMP <- coeftest(trumplm, vcov=vcovHC(trumplm, type="sss", cluster="group"))
BIDEN <- coeftest(bidenlm, vcov=vcovHC(bidenlm, type="sss", cluster="group")) 

#-----------------------------------------------------#
##MAKE REFERENCE DATASET USING COEFFICIENTS TO ADJUST CANDIDATES
#-----------------------------------------------------#
TC <- TRUMP[which(TRUMP[,4]<0.05),]
TC <- TC[,1]

names(TC) <- gsub("pollster|population|third_option|fb|meth", "", names(TC))

BC <- BIDEN[which(BIDEN[,4]<0.05),]
BC <- BC[,1]

names(BC) <- gsub("pollster|population|third_option|fb|meth", "", names(BC))

a <- wFB %>% 
  group_by(fb, answer, state) %>% 
  summarise(mean = mean(pct)) %>% 
  filter(state%in%c("Iowa","Georgia","Maine","Arizona","Maine","Michigan","North Carolina","Texas"),
         !(answer %in% c("Hawkins","Jorgensen"))) %>%
  ungroup()

a <- split(a, a$fb)

a <- data.frame(cbind(a$versus, a$fullBallot))
a$diff <- a$mean-a$mean.1

third_party_diff_biden <- a[1:7,] %>% select(state, diff)
third_party_diff_trump <- a[8:14,] %>% select(state, diff)

biden3_diff <- c(third_party_diff_biden$diff)
names(biden3_diff) <- c(third_party_diff_biden$state)

trump3_diff <- c(third_party_diff_trump$diff)
names(trump3_diff) <- c(third_party_diff_trump$state)

TC <- c(TC, trump3_diff)
BC <- c(BC, biden3_diff)


#-----------------------------------------------------#
##GENERATING PROBABILITY DATASET
#-----------------------------------------------------#
extra <- as.matrix(c("Maine CD-1", 
                     "Maine CD-2", 
                     "Nebraska CD-1", 
                     "Nebraska CD-2", 
                     "Nebraska CD-3",
                     "District of Columbia"), ncol=1)

colnames(extra) <- "State"
states_list <- rbind(states_list, extra)
states_list <- states_list %>% arrange(State)

uniqueState <- sort(unique(wFB$state))

get_probabilities_for_these <- states_list[,1][!states_list[,1] %in% uniqueState]
get_probabilities_for_these <- sort(get_probabilities_for_these, decreasing = T)

model538 <- model538 %>% select(state, prob=winstate_inc, modeldate) %>% 
  mutate(DATE = mdy(modeldate)) %>% 
  filter(DATE == c(max(DATE))) %>% 
  select(state, prob)

model538$state <- gsub("ME-", "Maine CD-",(model538$state))
model538$state <- gsub("NE-", "Nebraska CD-",(model538$state))

prob <- model538$prob[model538$state %in% c(get_probabilities_for_these)]
state <- get_probabilities_for_these
fetched_prob <- cbind(state, prob)

asdf <- as.matrix(sapply(unique(wFB$state), generate_state_probability, data = wFB, TC = TC, BC = BC))
generated_prob <- as.data.frame(cbind(names(asdf[,1]),asdf[,1]))
names(generated_prob) <- c("state", "prob")

probabilities <- as.data.frame(rbind(generated_prob, fetched_prob))
rownames(probabilities) <- NULL

probabilities <- left_join(probabilities, state_votes, by = c("state"))

#-----------------------------------------------------#
##RUNNING SIMULATION ACCORDING TO PROBABILITIES DATA
#-----------------------------------------------------#

final <- generate_simulations(probabilities, 1000)

prop.table(table(final$Winner))

#-----------------------------------------------------#
##MAKING PLOTS
#-----------------------------------------------------#

#making factors for easy chart creation
probabilities$prob <- as.character(round(as.numeric(probabilities$prob), digits = 6))

probabilities$class <- ifelse(probabilities$prob<.25,"Biden",
                              ifelse(probabilities$prob>=.25 & probabilities$prob<.4, "Lean Biden", 
                                     ifelse(probabilities$prob>=.4 & probabilities$prob<.6,"Tossup", 
                                            ifelse(probabilities$prob>=.6 & 
                                                     probabilities$prob<.8,"Lean Trump","Trump"))))

probabilities$color <- ifelse(probabilities$prob<.25,"dodgerblue4",
                              ifelse(probabilities$prob>=.25 & probabilities$prob<.4, "dodgerblue1", 
                                     ifelse(probabilities$prob>=.4 & probabilities$prob<.6,
                                            "gray68", 
                                            ifelse(probabilities$prob>=.6 & 
                                                     probabilities$prob<.8,"darksalmon","firebrick"))))

#Waffle Chart
a <- table(factor(sample(final$Winner, 100)))
a <- c(a[1], a[2], a[3])

a

waffle(a,10,
       xlab = "1 sq == 1 election simulation",
       title = paste("", "WINNER?", "\n", "Biden", a[1], "/", "Trump", a[3]),
       colors = c("dodgerblue4", "grey67", "firebrick"))

#now the map
map_data <- us_map()

#drawing boxes for extra CDs and DC on the map
extra_map <- data.frame(
  xmin=c(2500000, 2500000, 2500000, 2500000, 2500000, 2500000),
  xmax=c(2700000, 2700000, 2700000, 2700000, 2700000, 2700000),
  ymin=c(-175000, -200000, -400000, -600000, -800000, -1000000),
  ymax=c(1, -375000, -575000, -775000, -975000, -1175000),
  name=c("District of Columbia", "Maine CD-1", "Maine CD-2", "Nebraska CD-1", "Nebraska CD-2",
         "Nebraska CD-3")
)

#joining probabilities to both mapping data sets
extra_map <- left_join(extra_map,probabilities, by=c("name"="state"))

map_data <- left_join(map_data, probabilities, by = c("full" = "state"))

#creating labels dataset
map_labels <- data.frame(
  x = c(-1300000, -570000, 250000, 1100000, 1900000),
  y = c(750000, 750000, 750000, 750000, 750000),
  text = c("Biden", "Lean Biden", "Toss-up", "Lean Trump", "Trump"),
  color = c("dodgerblue4", "dodgerblue1", "gray68", "darksalmon", "firebrick")
)

#map
p <- ggplot()+
  geom_polygon(data = map_data,
               mapping = aes(x=x, y=y, group=group, 
                             text = paste(" ",full,"\n",
                                          "Likely winner: ", class, "\n",
                                          "Prob. of trump win: ", prob)),
               fill = map_data$color,
               color = "grey83")+
  scale_color_identity()+
  geom_rect(data = extra_map, 
            aes(xmin=xmin, xmax=xmax ,ymin=ymin ,ymax=ymax, 
                text = paste(" ",name, "\n",
                             "Likely winner: ",class, "\n", 
                             "Prob. of trump win: ", prob)),
            fill = extra_map$color, 
            inherit.aes = F)+
  geom_text(data = map_labels, mapping = aes(x=x, y=y, label = text), 
             color = map_labels$color)+
  labs(caption = paste("last updated: ", format(Sys.Date(), "%B %d, %Y")))+
  theme_void()

ggplotly(p) %>% config(displayModeBar = F)

#upload to plotly online
Sys.setenv("plotly_username"="#########")
Sys.setenv("plotly_api_key"="##################")

api_create(last_plot(), filename = "election_map", fileopt = "overwrite")

#Line Graph
daily_call <- data.frame(a["Biden"], a["Trump"], a["Tie"], as.character(Sys.Date()))
names(daily_call) <- c("Biden", "Trump", "Tie", "Date")
rownames(daily_call) <- NULL

line.data <- read.csv("ElectionPredictor/linegraphdata.csv")
line.data <- rbind(line.data, daily_call)

write.csv(line.data, "ElectionPredictor/linegraphdata.csv", row.names = FALSE)

long.line.data <- pivot_longer(line.data, cols = c("Biden", "Trump", "Tie"), values_to = "win")
names(long.line.data) <- c("Date", "Outcome", "Win Percentage")
long.line.data$Date <- as.Date(long.line.data$Date)

asdfasdf<- ggplot(data = long.line.data, aes(x = Date, y = `Win Percentage`))+
  geom_point(aes(color = Outcome))+
  geom_line(aes(color = Outcome))+
  scale_color_manual(values = c("dodgerblue4", "grey68", "firebrick"))+
  ylim(0,100)+
  scale_x_date(date_labels = "%d %b")+
  theme_minimal()

ggplotly(asdfasdf, tooltip = c("Outcome", "Win Percentage"))

#upload to plotly online
Sys.setenv("plotly_username"="#########")
Sys.setenv("plotly_api_key"="##################")

api_create(last_plot(), filename = "daily_tracker", fileopt = "overwrite")
